# JordanDiagramCheck

A `lake comparator` check of the main results of [`JordanDiagram`](../JordanDiagram/).

* [`Challenge.lean`](Challenge.lean): the **trusted** statements, each with `sorry`. This is the
  file to review. It says, in Lean, what the formalization claims.
* [`Solution.lean`](Solution.lean): the same statements, proved from the library.
* [`comparator.json`](../comparator.json), at the project root: the theorems to compare and the permitted axioms
  (`propext`, `Quot.sound`, `Classical.choice`).

A passing run means each Solution theorem has exactly the Challenge statement, uses only the
permitted axioms, and is accepted by the kernel.

## Statements

| Challenge theorem | Content |
| --- | --- |
| `terminal_determination` | Terminal determination: with injective terminal maps, `G_F(R) → Aut(J)` is injective with image `⋂ᵢ Stab(Aᵢ)` |
| `compatible_derivations` | Terminal determination for derivations: `g_F(R) → Der(J)` is injective with image `{D : D(Aᵢ) ⊆ Aᵢ}` |
| `wedge` | Wedges: restriction to the two halves is injective with image the pairs agreeing at the terminal dot |
| `iso_terminal_determination` | Terminal determination for isomorphisms: `F ≅ F'` corresponds to `h : J ≃ J'` with `h(Aᵢ) = A'ᵢ` |
| `finite_detector` | Finite detector criterion: a finite, stable, Jordan-generating `X ⊆ J` gives `\|G_F(R)\| ≤ \|X\|!` |
| `scalar_extension` | Commutativity and the Jordan identity on `S ⊗[R] A`, for Mathlib's product |
| `autMap_functor` | Functor laws for `G_F`, compatibility with `G_F(R) → G_F(S)` |
| `derMap_functor` | Functor laws for `g_F`, brackets preserved |
| `comparison_injective`, `comparison_image` | Injectivity and image of `G_F(R) → G_F(S)` when every `a ↦ 1 ⊗ a` is injective |
| `spinFactor_aut`, `spinFactor_der` | Spin-factor symmetries, stated elementarily: automorphisms are `(v, r) ↦ (g v, r)` with `g` an isometry, derivations are `(v, r) ↦ (X v, 0)` with `X` skew |
| `orthogonal_splitting` | Orthogonal splitting for one nonsingular member: `Stab_{O(V,B)}(W) ≃* O(W, B) × O(W⊥, B)` |
| `spin_diagram_group` | The automorphism group of a spin-factor diagram is the stabilizer of the `Wᵢ` in the orthogonal group |

The statements use the library's definitions (`JordanDiagram`, `autGroup`, `ev`, `derAlgebra`,
`autMap`, …), which are part of the trusted import closure. `Challenge.lean` imports the whole
library, so the check pins the statements and the axioms, but does not separate the trusted
definitions from the untrusted proofs in the library.

## Running

From the project root, which holds [`comparator.json`](../comparator.json):

```sh
lake comparator              # Lean's kernel
lake comparator --paranoid   # also every external kernel bundled with Lean
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
loads the project's `.olean` files into Lake itself.

Check done on this setup: replacing a Solution proof with `sorry` is rejected
("Illegal axiom detected: 'sorryAx'").
