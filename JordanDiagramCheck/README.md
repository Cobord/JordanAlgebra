# JordanDiagramCheck

A `lake comparator` check of the main results of [`JordanDiagram`](../JordanDiagram/).

* [`Challenge.lean`](Challenge.lean): the **trusted** statements, each with `sorry`. This is the
  file to review. It says, in Lean, what the formalization claims.
* [`Solution.lean`](Solution.lean): the same statements, proved from the library.
* [`comparator.json`](../comparator.json), at the project root, with the aggregate
  [`Challenge.lean`](../Challenge.lean) and [`Solution.lean`](../Solution.lean) that also collect
  [`JordanCheck`](../JordanCheck/): the theorems to compare and the permitted axioms
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
| `product_base_rings` | `(G_F(fst), G_F(snd)) : G_F(S × S') → G_F(S) × G_F(S')` is bijective |
| `power_series_specialization` | For finite free nodes and torsion-free `S`, the kernel of `G_F(S⟦X⟧) → G_F(S)` is torsion-free, finite subgroups embed, and the map is split by constant series |
| `derMap_functor` | Functor laws for `g_F`, brackets preserved |
| `comparison_injective`, `comparison_image` | Injectivity and image of `G_F(R) → G_F(S)` when every `a ↦ 1 ⊗ a` is injective |
| `family_functor` | For a family with coherent base-change maps `β_φ`, `G_F(φ)(g) ∘ β_φ = β_φ ∘ g` (likewise `g_F`), and `G_F`, `g_F` satisfy the functor laws |
| `baseChangeFamily_functor` | The family `S ↦ S ⊗ F` has the `G_F`, `g_F` of scalar extension |
| `family_base` | Every family is the scalar extension of its fiber over the base: `F_S ≅ S ⊗ F_R` via `1 ⊗ a ↦ β_{ι_S}(a)` |
| `ordered_coinitial` | An injective morphism of ordered scalars carries the positives onto a coinitial subset of the target's positives |
| `ordered_power_series` | In the lowest-coefficient order `t` is a positive infinitesimal; the constant-term map `A⟦t⟧ → A` is a morphism of ordered scalars; there is no morphism `A → A⟦t⟧` |
| `ordered_restriction` | `G_F`, `g_F` restricted to ordered scalars act through the underlying algebra maps |
| `spinFactor_aut`, `spinFactor_der` | Spin-factor symmetries, stated elementarily: automorphisms are `(v, r) ↦ (g v, r)` with `g` an isometry, derivations are `(v, r) ↦ (X v, 0)` with `X` skew |
| `orthogonal_splitting` | Orthogonal splitting for one nonsingular member: `Stab_{O(V,B)}(W) ≃* O(W, B) × O(W⊥, B)` |
| `orthogonal_flag` | Orthogonal flags: for `V = ⨁ Uⱼ` with mutually orthogonal pieces on which `B` is nondegenerate, the stabilizer of the flag `W_j = ⨆_{i ≤ j} Uᵢ` is `∏ⱼ O(Uⱼ, B)`, by restriction |
| `orthogonal_flag_iso` | Two orthogonal flags with nondegenerate pieces are isometric exactly when their pieces are pairwise isometric |
| `orthogonal_flag_lie` | The skew endomorphisms preserving an orthogonal flag are the families of skew endomorphisms of the pieces, by restriction |
| `twisted_exact_sequence` | For a diagram over a preorder, `1 → G_F → G̃_F → Aut(I)` is exact |
| `wreath_product` | The shape-twisted group of the wreath diagram (copies of a free `U` below `κ → U`) is `O(U)^κ ⋊ Perm κ`, with the shape map the permutation part |
| `spin_diagram_group` | The automorphism group of a spin-factor diagram is the stabilizer of the `Wᵢ` in the orthogonal group |
| `zHalf_hom` | A unital map `Z[1/2] → R` is unique, and exists exactly when `2` is a unit in `R` |
| `octonion_norm_coefficients` | The generalized octonion norm is diagonal with coefficients `1, -a, -b, ab, -c, ac, bc, -abc` |
| `octonion_norm_coefficients_pos` | These coefficients are positive over an ordered ring when `a, b, c < 0` |
| `shape_twisted_group` | For an arbitrary terminally pointed shape, `1 → G_F → G̃_F → Aut(I⁺, +)` is exact, and with injective terminal maps `G̃_F` is the group of pairs `(u, h)` with `h(Aᵢ) = A_{u(i)}` |
| `minkowski` | For every level `m ≥ 3`, an integer matrix `≡ 1 (mod m)` of finite order is `1`, so finite subgroups of `GL_N(ℤ)` embed in `GL_N(ℤ/m)` |
| `spinFactor_formallyReal_iff` | Over a real closed field, a spin factor is formally real exactly when its form is positive definite |
| `fraction_field_order` | A totally ordered ring is a domain, and its fraction field has a unique order extending it |
| `lattice_at_terminal` | A lattice at the terminal node determines the integral points of the diagram: `g₊(L) = L` iff `gᵢ(νᵢ⁻¹L) = νᵢ⁻¹L` for all `i`; the node lattices span and are finitely generated |

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
