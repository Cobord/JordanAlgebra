from __future__ import annotations

from itertools import combinations
from typing import List

VARS: List[str] = ["x", "y", "u", "v", "w"]


def mul_mul_eq_rule(b: str, c: str, d: str, p: str, q: str) -> str:
    """One instance of `mul_mul_eq (b c d z : M) : (b*d)*c*z = ...` with
    `z := p*q`, formatted as a `find_cancel.py` rewrite rule `LHS = RHS`."""
    z = f"{p}*{q}"
    lhs = f"({b}*{d})*{c}*({z})"
    rhs = (
        f"({b}*{d})*({c}*({z})) + ({c}*{d})*({b}*({z})) + ({b}*{c})*({d}*({z})) "
        f"- {b}*({c}*({d}*({z}))) - {d}*({c}*({b}*({z})))"
    )
    return f"{lhs} = {rhs}"


def generate_rules() -> List[str]:
    """All `mul_mul_eq` instances with (b, c, d) an ordered choice of 3 of the 5
    variables (b, d symmetric, so only the choice of `c` among the 3 matters)
    and z the product of the other 2 variables."""
    rules: List[str] = []
    for subset in combinations(VARS, 3):
        for c in subset:
            b, d = sorted(v for v in subset if v != c)
            p, q = sorted(v for v in VARS if v not in subset)
            rules.append(mul_mul_eq_rule(b, c, d, p, q))
    return rules


if __name__ == "__main__":
    for rule in generate_rules():
        print(rule)
