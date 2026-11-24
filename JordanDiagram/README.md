# JordanDiagram

Formalization of *Symmetries of Jordan Algebra Diagrams over Varying Base Rings* (the paper whose
earlier draft is in [`Beyond/`](../Beyond/)), built on the `Jordan` library. It follows the order
suggested in Remark B.4 of the paper. Scalar extension is done for a base map `R → S`
(`F ↦ S ⊗[R] F`), and the diagram automorphism groups form a functor
`G_F : CommAlgCat R ⥤ GrpCat` (`autFunctor`, Proposition 3.3). The family `{F_S}` is the one of
Lemma 2.11 (`F_S = S ⊗[R] F`); general families with arbitrary coherences `β_f` (Definition 2.8)
are not packaged as a structure.

## Design choices

* **Morphisms of `Jord_R`** are Mathlib's non-unital algebra homomorphisms `A →ₙₐ[R] B`
  (`R`-linear and product-preserving, with no unit condition). This allows corner inclusions
  (Lemma 8.14) as arrows.
* **Isomorphisms and automorphisms.** `A ≃ⱼ[R] B` (`JordanEquiv`) is a linear bijection preserving
  the product. Mathlib has no group structure on `A →ₙₐ[R] A`, so `Aut_{Jord_R}(A)` is
  `jordanAut R A`, the subgroup of `A ≃ₗ[R] A` of multiplicative maps; `JordanEquiv.autEquiv`
  identifies the two.
* **Diagrams** are recorded concretely (`JordanDiagram R I`: algebras `obj i`, maps `map α`,
  functoriality) and are not bundled as functors into a Mathlib category. The chosen terminal object
  is the class `TerminallyPointed I`, with an instance for preorders with a top element.
* **Monomorphisms.** Propositions 3.6 and 3.8 assume monic terminal maps. The paper's first step
  shows that these are injective, so here injectivity of each `νᵢ` is the hypothesis.
* **Shape-twisted automorphisms** over a functor `u` are isomorphisms `F ≅ u* F`
  (`TwistedIso F u`), which is the paper's description of a morphism over `(u, id_R)`.
* **Spin factors.** `SpinFactor.jordanAlgebra` is a definition that depends on `B.IsSymm`, so
  [`Algebra/SpinFactor.lean`](Algebra/SpinFactor.lean) adds a scoped instance under `[Fact B.IsSymm]`.
  A spin-factor diagram is indexed by any preorder with a top element, and its terminal node is
  `J(W ⊤, B|)`. The paper's case is `I = WithTop P` with `W ⊤ = V`.

## Files

The library has three parts:

* [`Algebra/`](Algebra/) concerns the symmetries of a single Jordan algebra, either generic or
  one of the algebras already formalized in `Jordan/`. Nothing in it mentions diagrams.
* [`MathlibMissing/`](MathlibMissing/) holds general constructions that Mathlib lacks and that
  the rest uses, candidates for upstreaming.
* [`Diagram/`](Diagram/) is the new content: terminally pointed diagrams, their automorphism
  groups and compatible derivations, and statements about them.

### `Algebra/`: symmetries of one algebra

| File | Paper | Contents |
| --- | --- | --- |
| [`Automorphism.lean`](Algebra/Automorphism.lean) | Def. 2.3 | `jordanAut R A`, setwise stabilizers `jordanAut.stab`, and lifting along an injective homomorphism: an automorphism or derivation of `J` that preserves `range ν` transports to `A` (`liftAut`, `liftDer`). |
| [`Equiv.lean`](Algebra/Equiv.lean) | Def. 2.3 | `JordanEquiv` (`A ≃ⱼ[R] B`) with `refl`, `symm`, `trans`. `JordanEquiv.lift`: an isomorphism `J ≃ⱼ J'` carrying `range ν` onto `range ν'` lifts along injective `ν`, `ν'`. |
| [`Generation.lean`](Algebra/Generation.lean) | input to Lemma 4.3 | `jordanAut.ext_of_adjoin_eq_top`: an automorphism is determined by its values on a generating set. |
| [`BaseChange.lean`](Algebra/BaseChange.lean) | Lemma 2.4 | With `2` invertible in `R`, `S ⊗[R] A` is a Jordan `S`-algebra (`instJordanAlgebra`). The proof goes through the fully linearized identity `lin`, which is multilinear, and `jordanExpr_add`. Also scalar extension of morphisms (`baseChangeHom`, injective for flat `S`), of automorphisms (`baseChangeAut`) and of derivations (`baseChangeDer`). Descent (`descendAut`): an automorphism of `E ⊗ A` preserving `1 ⊗ A` is `id ⊗ h` for an automorphism `h` of `A`, when `a ↦ 1 ⊗ a` is injective. |
| [`Functor.lean`](Algebra/Functor.lean) | Prop. 3.3 | Transport along any `φ : S →ₐ[R] T`: `mapLin φ f` is the unique `T`-linear map with `mapLin φ f ∘ (φ ⊗ 1) = (φ ⊗ 1) ∘ f`, and `mapAut φ : Aut(S ⊗ A) →* Aut(T ⊗ A)`. Functor laws `mapAut_id_alg`, `mapAut_comp_alg`, and `mapAut_baseChangeAut` (compatibility with extension from `R`). The same for derivations: `mapDer`, which is additive and bracket-preserving. |
| [`Orthogonal.lean`](Algebra/Orthogonal.lean) | Cor. 5.10 (one member) | If `B` is symmetric and nonsingular on `W`, then `V = W ⊕ W⊥` (`isCompl_orthogonal`), and `stabEquivProd : Stab_{O(V,B)}(W) ≃* O(W, B) × O(W⊥, B)`. |
| [`Tower.lean`](Algebra/Tower.lean) | Def. 2.8 (`β_f`); Prop. 3.3 | For `R → S → T`: the coherence `cancelJordanEquiv : T ⊗[S] (S ⊗[R] A) ≃ⱼ[T] T ⊗[R] A`, the extension `autTower : Aut(S ⊗ A) →* Aut(T ⊗ A)`, and `autTower_baseChangeAut`: extending from `R` to `S` and then to `T` is extending from `R` to `T`. |
| [`SpinFactor.lean`](Algebra/SpinFactor.lean) | Def. 5.2; Lemma 5.5 | For `V`, `V'` free, `2` invertible and any symmetric forms, including degenerate ones: `isometryEquiv : Isometry B B' ≃ (J(V, B) ≃ⱼ J(V', B'))` (`g ↦ g ⊕ id`), `autEquivOrthogonal : O(V, B)(R) ≃* Aut J(V, B)`, and `derEquivSkew : o(V, B)(R) ≃ Der J(V, B)` (`X ↦ X ⊕ 0`). |

### `MathlibMissing/`: general constructions not in Mathlib

| File | Contents |
| --- | --- |
| [`LieRingCat.lean`](MathlibMissing/LieRingCat.lean) | `LieRingHom L L'` (`L →⁅⁆ L'`): additive maps with bracket preservation as a field, with `id`, `comp`, `ext`, `map_lie`. `LieRingCat`, the category of Lie rings, with the same API as `GrpCat`. |
| [`PiLie.lean`](MathlibMissing/PiLie.lean) | The componentwise Lie ring and Lie algebra structures on a Pi type. |

### `Diagram/`: the diagram layer

| File | Paper | Contents |
| --- | --- | --- |
| [`Basic.lean`](Diagram/Basic.lean) | Defs. 2.5, 2.8 | `TerminallyPointed`, `JordanDiagram`, restriction along a functor, the terminal algebra `J`, the terminal maps `ν i` and the terminal relation `ν_map`, and the images `Aᵢ`. |
| [`Group.lean`](Diagram/Group.lean) | Defs. 3.1, 3.4; Prop. 3.6; Lemma 3.11 | The diagram automorphism group `autGroup`, terminal evaluation `ev`, and terminal determination: `ev_injective`, `range_ev`, and `autGroupEquivStab : G_F(R) ≃* ⋂ᵢ Stab(Aᵢ)`. Also `restrictHom`. |
| [`Derivation.lean`](Diagram/Derivation.lean) | Def. 3.7; Prop. 3.8; Lemma 3.11 | The compatible derivations `derAlgebra` as a Lie subalgebra, the Lie homomorphism `evDer`, `evDer_injective`, `range_evDer` (image `{D : D(Aᵢ) ⊆ Aᵢ}`), and `restrictDer`. |
| [`Wedge.lean`](Diagram/Wedge.lean) | Prop. 3.12 | `IsWedge P₁ P₂` and `autGroupEquivWedge : G_F(R) ≃* G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)`. For derivations, `wedgeDer_injective` and `range_wedgeDer`. |
| [`Iso.lean`](Diagram/Iso.lean) | Prop. 2.7 (fibers); Def. 3.13; Prop. 3.14 | `DiagramIso F F'` and its terminal determination `terminalEquiv` (isomorphisms `↔` `h : J ≃ⱼ J'` with `h(Aᵢ) = A'ᵢ`). `TwistedIso F u = DiagramIso F (u* F)`. `twistedIdEquiv` identifies the twisted isomorphisms over `𝟭` with `G_F(R)`, the kernel in Prop. 3.14. `twistedTerminalEquiv` is the terminal description in Prop. 3.14. |
| [`Finiteness.lean`](Diagram/Finiteness.lean) | Prop. 4.2; Lemma 4.3 | The finite detector criterion: a faithful action on a finite `X` gives `\|G\| ≤ \|X\|!`. `card_autGroup_le`: a finite, stable, Jordan-generating `X ⊆ J` bounds `\|G_F(R)\|` by `\|X\|!`. |
| [`SpinFactor.lean`](Diagram/SpinFactor.lean) | Def. 5.3; Lemma 5.4; Props. 5.6, 5.7 | `spinDiagram B W` for monotone `W : I →o Submodule R V`. Its terminal maps are injective, with image `R 1 ⊕ Wᵢ`. `spinDiagramAutEquiv : G_F(R) ≃* Stab_{O(W ⊤, B)}(W)`, `spinDiagramDerEquiv : g_F(R) ≃ Stab_{o(W ⊤, B)}(W)`, and `spinDiagramIsoEquiv`: isomorphisms of spin-factor diagrams are isometries of the configurations. |
| [`Functor.lean`](Diagram/Functor.lean) | Prop. 3.3 | **The functor `G_F`**: `autFunctor F : CommAlgCat R ⥤ GrpCat`, `S ↦ Aut(S ⊗[R] F)`, built from `autMap F φ : G_F(S) →* G_F(T)` with `autMap_id`, `autMap_comp`, and `autMap_comp_autBaseChange`. For `R = Z[1/2]`, `CommAlgCat R` is the paper's `CAlg_{Z[1/2]}`. **The functor `g_F`**: `derFunctor F : CommAlgCat R ⥤ LieRingCat`, built from the Lie ring homomorphisms `derMap F φ : g_F(S) →⁅⁆ g_F(T)` with `derMap_id`, `derMap_comp`, and `derMap_derBaseChange`. |
| [`BaseChange.lean`](Diagram/BaseChange.lean) | Lemma 2.11; Props. 3.3, 7.9(b), 7.9(c); Cor. 7.10 | `F.baseChange S = S ⊗[R] F`. `autBaseChange : G_F(R) →* G_F(S)`, injective when every `F(i) → S ⊗ F(i)` is (`autBaseChange_injective`). Its image is the set of automorphisms preserving every `1 ⊗ F(i)` (`range_autBaseChange`, Prop. 7.9(c)), with `autGroupEquivPreserving` (Cor. 7.10). `autTowerDiagram : G_F(S) →* G_F(T)` for `R → S → T`, and `autTowerDiagram_comp_autBaseChange`: it composes with `G_F(R) → G_F(S)` to give `G_F(R) → G_F(T)` (Prop. 3.3). `derBaseChange` on compatible derivations, additive and bracket-preserving. Terminal maps stay injective along flat `R → S`. |

Build with `lake build JordanDiagram`. The default target is still the `jordan` executable. There
are no `sorry`s. The headline results use only `propext`, `Classical.choice` and `Quot.sound`.

## Next steps

1. The families of Def. 2.8 with arbitrary coherences `β_f` packaged as data, and `G_F`, `g_F`
   for them.
2. Spin-factor flags: Corollary 5.10 (orthogonal decomposition, `G_F ≅ ∏ O(Uⱼ)`) and the wreath
   product of Example 5.9.
3. The group structure on all of `G̃_F(R)`, with `u` ranging over `Aut(I⁺, +)`.
4. The ordered layer (Section 6). `IsFormallyReal` already exists separately in `Jordan/`.
