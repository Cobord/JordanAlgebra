from __future__ import annotations

import argparse
import ast
from collections import defaultdict
from fractions import Fraction
from typing import Dict, List, Literal, Optional, Tuple, Union

Number = Union[int, float, Fraction]
# A leaf term: a numeric coefficient paired with the product tree it scales
# (or None when the leaf is a pure number, e.g. the `2` in `2 * a * b`).
Term = Tuple[Number, Optional[ast.expr]]


def expand(node: ast.expr) -> List[Term]:
    """Fully distribute +,-,* into a flat list of (coeff, product_node), where
    product_node contains only Mult/Name (no Add/Sub left inside), or is None
    for a pure numeric term. Numeric literals and unary minus are folded into
    `coeff`."""
    if isinstance(node, ast.Constant):
        if not isinstance(node.value, (int, float)):
            raise ValueError(f"unsupported constant {node.value!r}")
        return [(node.value, None)]
    if isinstance(node, ast.Name):
        return [(1, node)]
    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.USub):
            return [(-c, n) for c, n in expand(node.operand)]
        if isinstance(node.op, ast.UAdd):
            return expand(node.operand)
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Add):
            return expand(node.left) + expand(node.right)
        if isinstance(node.op, ast.Sub):
            right = expand(node.right)
            return expand(node.left) + [(-c, n) for c, n in right]
        if isinstance(node.op, ast.Mult):
            left_terms = expand(node.left)
            right_terms = expand(node.right)
            result: List[Term] = []
            for cl, nl in left_terms:
                for cr, nr in right_terms:
                    coeff = cl * cr
                    prod: Optional[ast.expr]
                    if nl is None:
                        prod = nr
                    elif nr is None:
                        prod = nl
                    else:
                        prod = ast.BinOp(left=nl, op=ast.Mult(), right=nr)
                    result.append((coeff, prod))
            return result
    raise ValueError(f"unexpected node {ast.dump(node)}")


def flatten(node: ast.expr, side_sign: int = 1) -> List[Term]:
    return [(side_sign * c, n) for c, n in expand(node)]


def canon(node: Optional[ast.expr]) -> str:
    """Canonical string for a product tree, commutative at every Mul node."""
    if node is None:
        return "1"
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        l = canon(node.left)
        r = canon(node.right)
        a, b = sorted([l, r])
        return f"({a}*{b})"
    raise ValueError(f"unexpected in canon {ast.dump(node)}")


def pretty(node: Optional[ast.expr]) -> str:
    if node is None:
        return "1"
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return f"({pretty(node.left)}*{pretty(node.right)})"
    raise ValueError(f"unexpected in pretty {ast.dump(node)}")


def coeff_str(coeff: Number) -> str:
    if isinstance(coeff, Fraction):
        sign = "-" if coeff < 0 else "+"
        return f"{sign}{abs(coeff)}"
    return f"{coeff:+g}"


def term_str(coeff: Number, node: Optional[ast.expr]) -> str:
    body = pretty(node)
    if coeff == 1:
        return f"+{body}"
    if coeff == -1:
        return f"-{body}"
    return f"{coeff_str(coeff)}*{body}"


def get_terms(src: str, side_sign: int) -> List[Term]:
    tree = ast.parse(src.strip(), mode="eval")
    return flatten(tree.body, side_sign)


Rule = Tuple[str, List[Term]]


def parse_rule(rule_src: str) -> Rule:
    """Parse a rewrite rule `LHS = RHS`: LHS must canonicalize to a single product
    term (coefficient 1), used as a lookup key. If the LHS shape also occurs
    (with net coefficient `k`) among the expanded RHS terms, that isn't already a
    usable substitution -- `LHS = k*LHS + rest` really means `(1-k)*LHS = rest`,
    i.e. `LHS = rest / (1-k)` -- so this solves for LHS algebraically (using
    exact `Fraction` arithmetic) rather than naively substituting a
    self-referential rule, which would silently "move it over and divide" (or
    worse, if `k = 1`, assert the leftover terms sum to zero)."""
    if "=" not in rule_src:
        raise ValueError("rewrite rule must have the form 'LHS = RHS'")
    lhs_src, rhs_src = rule_src.split("=", 1)
    lhs_tree = ast.parse(lhs_src.strip(), mode="eval").body
    lhs_terms = expand(lhs_tree)
    if len(lhs_terms) != 1 or lhs_terms[0][0] != 1:
        raise ValueError("rewrite rule LHS must be a single term with coefficient 1")
    _, lhs_node = lhs_terms[0]
    rule_lhs_canon = canon(lhs_node)
    rhs_terms = get_terms(rhs_src, 1)

    matching = [c for c, n in rhs_terms if canon(n) == rule_lhs_canon]
    remaining = [(c, n) for c, n in rhs_terms if canon(n) != rule_lhs_canon]
    if not matching:
        return rule_lhs_canon, remaining

    k = sum(matching)
    denom = 1 - k
    if denom == 0:
        raise ValueError(
            "cannot solve rule for its LHS: the RHS's coefficient of the LHS "
            "shape is exactly 1, so this equation asserts the remaining terms "
            "sum to zero, not a definition of the LHS"
        )
    if denom == 1:
        return rule_lhs_canon, remaining
    solved = [(Fraction(c) / denom, n) for c, n in remaining]
    return rule_lhs_canon, solved


def apply_rule(terms: List[Term], rule: Rule) -> List[Term]:
    """Rewrite every leaf term whose canonical form matches the rule's LHS,
    substituting in the rule's (already-solved, non-self-referential) RHS,
    scaled by the leaf's coefficient. A single pass suffices."""
    rule_lhs_canon, rule_rhs = rule
    result: List[Term] = []
    for coeff, node in terms:
        if canon(node) == rule_lhs_canon:
            result.extend((coeff * rc, rn) for rc, rn in rule_rhs)
        else:
            result.append((coeff, node))
    return result


CancelStats = Tuple[int, int, int]  # (fully_cancelled, total_terms, remaining_forms)


def find_cancellations(
    lhs_src: str,
    rhs_src: str,
    rule_srcs: Optional[List[str]] = None,
    verbose: bool = True,
) -> CancelStats:
    """Parse `lhs_src = rhs_src`, move everything to one side (LHS - RHS), fully
    distribute +,-,* into leaf terms (each with a numeric coefficient), then
    group leaves by their commutation-equivalence class (product trees equal up
    to swapping children at each `*` node, keeping the same association/bracket
    shape). When `verbose`, prints which groups fully cancel (net coefficient 0)
    and which have a nonzero net contribution; always returns the summary stats
    `(fully_cancelled, total_terms, remaining_forms)`.

    If `rule_srcs` (each a string `LHS = RHS`) is given, they're applied in
    order: every leaf term matching a rule's LHS (up to commutation) is
    substituted with that rule's RHS expansion before moving on to the next
    rule and then grouping -- e.g. to try out algebraic identities like
    `mul_mul_eq` and see what they cancel against, individually or combined."""
    lhs_terms = get_terms(lhs_src, 1)
    rhs_terms = get_terms(rhs_src, -1)  # move to LHS - RHS = 0
    all_terms = lhs_terms + rhs_terms

    for rule_src in rule_srcs or []:
        rule = parse_rule(rule_src)
        all_terms = apply_rule(all_terms, rule)

    if verbose:
        print(f"Total terms (LHS - RHS expanded): {len(all_terms)}")
        print()

    groups: Dict[str, List[Tuple[int, Number, Optional[ast.expr]]]] = defaultdict(list)
    for idx, (coeff, node) in enumerate(all_terms):
        c = canon(node)
        groups[c].append((idx, coeff, node))

    fully_cancelled = 0
    remaining_terms = 0
    if verbose:
        print("=== Groups (by commutation-equivalence class) ===")
    for c, entries in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        net = sum(coeff for _, coeff, _ in entries)
        if verbose:
            tag = "CANCELS" if net == 0 else f"NET={net:+g}"
            origs = ", ".join(term_str(coeff, n) for _, coeff, n in entries)
            print(f"[{tag}] canon={c}  terms: {origs}")
        if net == 0:
            fully_cancelled += len(entries)
        else:
            remaining_terms += 1

    if verbose:
        print()
        print(f"Terms fully cancelled: {fully_cancelled} / {len(all_terms)}")
        print(f"Distinct canonical forms with nonzero net: {remaining_terms}")

    return fully_cancelled, len(all_terms), remaining_terms


RuleLineArg = Union[int, Literal["all"], List[int]]


def parse_rule_line_arg(value: str) -> RuleLineArg:
    if value == "all":
        return "all"
    if "," in value:
        return [int(v) for v in value.split(",")]
    return int(value)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Find commutation-equivalent cancelling terms between two "
        "Lean +,-,*,() expressions (treated as an LHS = RHS goal). Supports "
        "numeric coefficients, e.g. '2 * a * b * c - 3 * b'."
    )
    parser.add_argument("lhs_file", help="path to file containing the LHS expression")
    parser.add_argument("rhs_file", help="path to file containing the RHS expression")
    parser.add_argument(
        "--rule",
        dest="rule_file",
        help="path to a file containing one or more rewrite rules 'LHS = RHS' "
        "(LHS a single term), one per (non-blank) line",
    )
    parser.add_argument(
        "--rule-line",
        dest="rule_line",
        type=parse_rule_line_arg,
        default=1,
        help="1-indexed line (counting only non-blank lines) of --rule to use as "
        "the rule to apply (default: 1), or 'all' to try every line one at a "
        "time and print a summary for each",
    )
    args = parser.parse_args()
    rule_line: RuleLineArg = args.rule_line
    with open(args.lhs_file) as f:
        lhs_src = f.read()
    with open(args.rhs_file) as f:
        rhs_src = f.read()

    def rule_at(line_num: int, rule_lines: List[str]) -> str:
        if not 1 <= line_num <= len(rule_lines):
            raise SystemExit(
                f"--rule-line {line_num} out of range: {args.rule_file} has "
                f"{len(rule_lines)} non-blank line(s)"
            )
        return rule_lines[line_num - 1]

    if args.rule_file is None:
        find_cancellations(lhs_src, rhs_src, None)
    else:
        with open(args.rule_file) as f:
            rule_lines = [line for line in f if line.strip()]
        if rule_line == "all":
            for i, rule_line_src in enumerate(rule_lines, start=1):
                cancelled, total, remaining = find_cancellations(
                    lhs_src, rhs_src, [rule_line_src], verbose=False
                )
                print(
                    f"[line {i:2d}] {cancelled:3d}/{total:3d} cancelled, "
                    f"{remaining:3d} forms remain  ::  {rule_line_src.strip()}"
                )
        elif isinstance(rule_line, list):
            selected = [rule_at(n, rule_lines) for n in rule_line]
            find_cancellations(lhs_src, rhs_src, selected)
        else:
            find_cancellations(lhs_src, rhs_src, [rule_at(rule_line, rule_lines)])
