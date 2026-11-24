# JordanDiagramCheck

A `lake comparator` check of the main results of [`JordanDiagram`](../JordanDiagram/).

* [`Challenge.lean`](Challenge.lean): the **trusted** statements, each with `sorry`. This is the
  file to review. It says, in Lean, what the formalization claims about the paper.
* [`Solution.lean`](Solution.lean): the same statements, proved from the library.
* [`comparator.json`](comparator.json): the theorems to compare and the permitted axioms
  (`propext`, `Quot.sound`, `Classical.choice`).

A passing run means each Solution theorem has exactly the Challenge statement, uses only the
permitted axioms, and is accepted by the kernel.

## Statements

| Challenge theorem | Paper |
| --- | --- |
| `terminal_determination` | Prop. 3.6 |
| `compatible_derivations` | Prop. 3.8 |
| `wedge` | Prop. 3.12 |
| `iso_terminal_determination` | Props. 3.14, 5.7 (terminal determination for isomorphisms) |
| `finite_detector` | Prop. 4.2 with Lemma 4.3 |
| `scalar_extension` | Lemma 2.4 (commutativity and the Jordan identity on `S ⊗[R] A`, for Mathlib's product) |
| `autMap_functor` | Prop. 3.3 (functor laws for `G_F`, compatibility with `G_F(R) → G_F(S)`) |
| `derMap_functor` | Prop. 3.8 (functor laws for `g_F`, brackets preserved) |
| `comparison_injective`, `comparison_image` | Prop. 7.9(b), 7.9(c) |
| `spinFactor_aut`, `spinFactor_der` | Lemma 5.5, stated elementarily: automorphisms are `(v, r) ↦ (g v, r)` with `g` an isometry, derivations are `(v, r) ↦ (X v, 0)` with `X` skew |
| `orthogonal_splitting` | Cor. 5.10, one nonsingular member |
| `spin_diagram_group` | Prop. 5.6 |

The statements use the library's definitions (`JordanDiagram`, `autGroup`, `ev`, `derAlgebra`,
`autMap`, …), which are part of the trusted import closure. `Challenge.lean` imports the whole
library, so the check pins the statements and the axioms, but does not separate the trusted
definitions from the untrusted proofs in the library.

## Running

```sh
JordanDiagramCheck/run.sh              # lake comparator, inside systemd-run
JordanDiagramCheck/run.sh --paranoid   # also every external kernel bundled with Lean
lake comparator --config JordanDiagramCheck/comparator.json   # directly
```

`lake comparator` needs Lean v4.35.0 or later. The expected output ends with

```
Lean default kernel accepts the solution
Your solution is okay!
```

With `--paranoid`, the solution is also accepted by Lean's paranoid kernel, `lean4lean`,
`nanoda`, `con-leche` and `con-ron`.

## Sandbox

`lake comparator` builds and exports the project inside its own bubblewrap sandbox, and never
loads the project's `.olean` files into Lake itself. `run.sh` additionally runs it under
`systemd-run -p RestrictAddressFamilies=~AF_UNIX`, so no step can connect to a Unix socket
(Docker, D-Bus, and so on) that stays visible on the read-only filesystem.

Checks done on this setup:
* replacing a Solution proof with `sorry` is rejected ("Illegal axiom detected: 'sorryAx'");
* `socket(AF_UNIX)` fails inside the `systemd-run` layer ("Address family not supported").
