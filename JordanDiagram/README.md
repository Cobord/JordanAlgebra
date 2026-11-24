# JordanDiagram

Formalization of *Symmetries of Jordan Algebra Diagrams over Varying Base Rings* (an earlier
draft is in [`Beyond/`](../Beyond/)), built on the `Jordan` library. Scalar extension is done for
a base map `R → S` (`F ↦ S ⊗[R] F`), and the diagram automorphism groups form a functor
`G_F : CommAlgCat R ⥤ GrpCat` (`autFunctor`). The family `{F_S}` is the scalar-extension family
`F_S = S ⊗[R] F`; general families with arbitrary coherences `β_f` are not packaged as a
structure.

## Design choices

* **Morphisms of `Jord_R`** are Mathlib's non-unital algebra homomorphisms `A →ₙₐ[R] B`
  (`R`-linear and product-preserving, with no unit condition). This allows corner inclusions
  as arrows.
* **Isomorphisms and automorphisms.** `A ≃ⱼ[R] B` (`JordanEquiv`) is a linear bijection preserving
  the product. Mathlib has no group structure on `A →ₙₐ[R] A`, so `Aut_{Jord_R}(A)` is
  `jordanAut R A`, the subgroup of `A ≃ₗ[R] A` of multiplicative maps; `JordanEquiv.autEquiv`
  identifies the two.
* **Diagrams** are recorded concretely (`JordanDiagram R I`: algebras `obj i`, maps `map α`,
  functoriality) and are not bundled as functors into a Mathlib category. The chosen terminal object
  is the class `TerminallyPointed I`, with an instance for preorders with a top element.
* **Monomorphisms.** Terminal determination can be stated for monic terminal maps. Monomorphisms
  of `Jord_R` are injective, so here injectivity of each `νᵢ` is the hypothesis.
* **Shape-twisted automorphisms** over a functor `u` are isomorphisms `F ≅ u* F`
  (`TwistedIso F u`), which describe the morphisms over `(u, id_R)`.
* **Spin factors.** `SpinFactor.jordanAlgebra` is a definition that depends on `B.IsSymm`, so
  [`Algebra/SpinFactor.lean`](Algebra/SpinFactor.lean) adds a scoped instance under `[Fact B.IsSymm]`.
  A spin-factor diagram is indexed by any preorder with a top element, and its terminal node is
  `J(W ⊤, B|)`. For example `I = WithTop P` with `W ⊤ = V`.

## Files

The library has three parts:

* [`Algebra/`](Algebra/) concerns the symmetries of a single Jordan algebra, either generic or
  one of the algebras already formalized in `Jordan/`. Nothing in it mentions diagrams.
* [`MathlibMissing/`](MathlibMissing/) holds general constructions that Mathlib lacks and that
  the rest uses, candidates for upstreaming.
* [`Diagram/`](Diagram/) is the new content: terminally pointed diagrams, their automorphism
  groups and compatible derivations, and statements about them.

### `Algebra/`: symmetries of one algebra

| File | Contents |
| --- | --- |
| [`Automorphism.lean`](Algebra/Automorphism.lean) | `jordanAut R A`, setwise stabilizers `jordanAut.stab`, and lifting along an injective homomorphism: an automorphism or derivation of `J` that preserves `range ν` transports to `A` (`liftAut`, `liftDer`). |
| [`Equiv.lean`](Algebra/Equiv.lean) | `JordanEquiv` (`A ≃ⱼ[R] B`) with `refl`, `symm`, `trans`. `JordanEquiv.lift`: an isomorphism `J ≃ⱼ J'` carrying `range ν` onto `range ν'` lifts along injective `ν`, `ν'`. |
| [`Generation.lean`](Algebra/Generation.lean) | `jordanAut.ext_of_adjoin_eq_top`: an automorphism is determined by its values on a generating set (the single-algebra input to the finite detector criterion). |
| [`BaseChange.lean`](Algebra/BaseChange.lean) | With `2` invertible in `R`, `S ⊗[R] A` is a Jordan `S`-algebra (`instJordanAlgebra`). The proof goes through the fully linearized identity `lin`, which is multilinear, and `jordanExpr_add`. Also scalar extension of morphisms (`baseChangeHom`, injective for flat `S`), of automorphisms (`baseChangeAut`) and of derivations (`baseChangeDer`). Descent (`descendAut`): an automorphism of `E ⊗ A` preserving `1 ⊗ A` is `id ⊗ h` for an automorphism `h` of `A`, when `a ↦ 1 ⊗ a` is injective. |
| [`Functor.lean`](Algebra/Functor.lean) | Transport along any `φ : S →ₐ[R] T`: `mapLin φ f` is the unique `T`-linear map with `mapLin φ f ∘ (φ ⊗ 1) = (φ ⊗ 1) ∘ f`, and `mapAut φ : Aut(S ⊗ A) →* Aut(T ⊗ A)`. Functor laws `mapAut_id_alg`, `mapAut_comp_alg`, and `mapAut_baseChangeAut` (compatibility with extension from `R`). The same for derivations: `mapDer`, which is additive and bracket-preserving. |
| [`Orthogonal.lean`](Algebra/Orthogonal.lean) | If `B` is symmetric and nonsingular on `W`, then `V = W ⊕ W⊥` (`isCompl_orthogonal`), and `stabEquivProd : Stab_{O(V,B)}(W) ≃* O(W, B) × O(W⊥, B)`. |
| [`OrthogonalFlag.lean`](Algebra/OrthogonalFlag.lean) | For an internal direct sum `V = ⨁ Uᵢ` of mutually orthogonal pieces: `stabPiecesEquivPi : Stab_{O(V,B)}(Uᵢ ∀ i) ≃* ∏ᵢ O(Uᵢ, B)`. With `B` nondegenerate on each piece and a linear order on the indices, `stabFlagEquivPi` gives the same for the flag `W_j = ⨆_{i ≤ j} Uᵢ`. |
| [`OrthogonalFlagIso.lean`](Algebra/OrthogonalFlagIso.lean) | `nonempty_flagIsometry_iff`: two orthogonal flags with nondegenerate pieces are isometric exactly when their pieces are pairwise isometric. `skewFlagEquivPi`: the skew endomorphisms preserving the flag are `⊕ᵢ o(Uᵢ, B)`, by restriction (the Lie algebra analogue). |
| [`Tower.lean`](Algebra/Tower.lean) | For `R → S → T`: the coherence `cancelJordanEquiv : T ⊗[S] (S ⊗[R] A) ≃ⱼ[T] T ⊗[R] A`, the extension `autTower : Aut(S ⊗ A) →* Aut(T ⊗ A)`, and `autTower_baseChangeAut`: extending from `R` to `S` and then to `T` is extending from `R` to `T`. |
| [`SpinFactor.lean`](Algebra/SpinFactor.lean) | For `V`, `V'` free, `2` invertible and any symmetric forms, including degenerate ones: `isometryEquiv : Isometry B B' ≃ (J(V, B) ≃ⱼ J(V', B'))` (`g ↦ g ⊕ id`), `autEquivOrthogonal : O(V, B)(R) ≃* Aut J(V, B)`, and `derEquivSkew : o(V, B)(R) ≃ Der J(V, B)` (`X ↦ X ⊕ 0`). |

### `MathlibMissing/`: general constructions not in Mathlib

| File | Contents |
| --- | --- |
| [`LieRingCat.lean`](MathlibMissing/LieRingCat.lean) | `LieRingHom L L'` (`L →⁅⁆ L'`): additive maps with bracket preservation as a field, with `id`, `comp`, `ext`, `map_lie`. `LieRingCat`, the category of Lie rings, with the same API as `GrpCat`. |
| [`PiLie.lean`](MathlibMissing/PiLie.lean) | The componentwise Lie ring and Lie algebra structures on a Pi type. |
| [`PowerSeriesMatrix.lean`](MathlibMissing/PowerSeriesMatrix.lean) | `Matrix.eq_one_of_pow_eq_one`: over a torsion-free `R`, a matrix over `R⟦X⟧` with constant term `1` and finite order is `1` (the kernel of `GL_n(R⟦X⟧) → GL_n(R)` is torsion-free). |

### `Diagram/`: the diagram layer

| File | Contents |
| --- | --- |
| [`Basic.lean`](Diagram/Basic.lean) | `TerminallyPointed`, `JordanDiagram`, restriction along a functor, the terminal algebra `J`, the terminal maps `ν i` and the terminal relation `ν_map`, and the images `Aᵢ`. |
| [`Group.lean`](Diagram/Group.lean) | The diagram automorphism group `autGroup`, terminal evaluation `ev`, and terminal determination: `ev_injective`, `range_ev`, and `autGroupEquivStab : G_F(R) ≃* ⋂ᵢ Stab(Aᵢ)`. Also `restrictHom`. |
| [`Derivation.lean`](Diagram/Derivation.lean) | The compatible derivations `derAlgebra` as a Lie subalgebra, the Lie homomorphism `evDer`, `evDer_injective`, `range_evDer` (image `{D : D(Aᵢ) ⊆ Aᵢ}`), and `restrictDer`. |
| [`Wedge.lean`](Diagram/Wedge.lean) | `IsWedge P₁ P₂` and `autGroupEquivWedge : G_F(R) ≃* G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)`. For derivations, `wedgeDer_injective` and `range_wedgeDer`. |
| [`Iso.lean`](Diagram/Iso.lean) | `DiagramIso F F'` (isomorphisms in a fiber) and its terminal determination `terminalEquiv` (isomorphisms `↔` `h : J ≃ⱼ J'` with `h(Aᵢ) = A'ᵢ`). `TwistedIso F u = DiagramIso F (u* F)`. `twistedIdEquiv` identifies the twisted isomorphisms over `𝟭` with `G_F(R)`, the kernel of `G̃_F(R) → Aut(I⁺, +)`. `twistedTerminalEquiv` is terminal determination for twisted automorphisms. |
| [`Product.lean`](Diagram/Product.lean) | `prodAutEquiv : Aut((S × S') ⊗ A) ≃* Aut(S ⊗ A) × Aut(S' ⊗ A)` and **`autGroupProdEquiv : G_F(S × S') ≃* G_F(S) × G_F(S')`**, the map being `(G_F(fst), G_F(snd))` (`autMap_prod_bijective`). |
| [`PowerSeries.lean`](Diagram/PowerSeries.lean) | The constant-term map `constCoeffAlg : S⟦X⟧ → S`, split by `constAlg`. For finite free nodes and torsion-free `S`: the kernel of `G_F(S⟦X⟧) → G_F(S)` is torsion-free (`autMap_const_eq_one`), finite subgroups embed (`injOn_autMap_const`), and the map is split (`autMap_const_comp_autMap_C`). |
| [`Twisted.lean`](Diagram/Twisted.lean) | For a shape that is a preorder: `TwistedAut F` (an order automorphism `σ` of the shape with Jordan isomorphisms `F(i) ≃ F(σ i)` compatible with the arrows) and its group structure, **the shape-twisted group `G̃_F(R)`**. `shapeHom : G̃_F(R) →* Aut(I)` and `ofAut : G_F(R) →* G̃_F(R)`, with `ofAut_injective` and `range_ofAut`: `1 → G_F(R) → G̃_F(R) → Aut(I)` is exact. `toTwistedIso`/`ofTwistedIso` relate it to `TwistedIso`. |
| [`Wreath.lean`](Diagram/Wreath.lean) | `spinTwist`: a shape automorphism `σ` and an isometry with `g(Wᵢ) = W_{σ i}` give a twisted automorphism `g ⊕ id` of a spin-factor diagram. `Disc κ` (discrete order), with `permShape_surjective`: every automorphism of `WithTop (Disc κ)` is a permutation. `wreathDiagram BU κ` (copies of `U` below `κ → U`) and **`wreathEquiv : G̃_F(R) ≃* O(U)^κ ⋊ Perm κ`**, with the shape map the permutation part. |
| [`Finiteness.lean`](Diagram/Finiteness.lean) | The finite detector criterion: a faithful action on a finite `X` gives `\|G\| ≤ \|X\|!`. `card_autGroup_le`: a finite, stable, Jordan-generating `X ⊆ J` bounds `\|G_F(R)\|` by `\|X\|!`. |
| [`SpinFactor.lean`](Diagram/SpinFactor.lean) | `spinDiagram B W` for monotone `W : I →o Submodule R V`. Its terminal maps are injective, with image `R 1 ⊕ Wᵢ`. `spinDiagramAutEquiv : G_F(R) ≃* Stab_{O(W ⊤, B)}(W)`, `spinDiagramDerEquiv : g_F(R) ≃ Stab_{o(W ⊤, B)}(W)`, and `spinDiagramIsoEquiv`: isomorphisms of spin-factor diagrams are isometries of the configurations. |
| [`Functor.lean`](Diagram/Functor.lean) | **The functor `G_F`**: `autFunctor F : CommAlgCat R ⥤ GrpCat`, `S ↦ Aut(S ⊗[R] F)`, built from `autMap F φ : G_F(S) →* G_F(T)` with `autMap_id`, `autMap_comp`, and `autMap_comp_autBaseChange`. For `R = Z[1/2]`, `CommAlgCat R` is `CAlg_{Z[1/2]}`. **The functor `g_F`**: `derFunctor F : CommAlgCat R ⥤ LieRingCat`, built from the Lie ring homomorphisms `derMap F φ : g_F(S) →⁅⁆ g_F(T)` with `derMap_id`, `derMap_comp`, and `derMap_derBaseChange`. |
| [`BaseChange.lean`](Diagram/BaseChange.lean) | `F.baseChange S = S ⊗[R] F`. `autBaseChange : G_F(R) →* G_F(S)`, injective when every `F(i) → S ⊗ F(i)` is (`autBaseChange_injective`). Its image is the set of automorphisms preserving every `1 ⊗ F(i)` (`range_autBaseChange`), with `autGroupEquivPreserving`. `autTowerDiagram : G_F(S) →* G_F(T)` for `R → S → T`, and `autTowerDiagram_comp_autBaseChange`: it composes with `G_F(R) → G_F(S)` to give `G_F(R) → G_F(T)`. `derBaseChange` on compatible derivations, additive and bracket-preserving. Terminal maps stay injective along flat `R → S`. |

Build with `lake build JordanDiagram`. The default target is still the `jordan` executable. There
are no `sorry`s. The headline results use only `propext`, `Classical.choice` and `Quot.sound`.

## Next steps

1. General families `{F_S}` over varying base rings, with arbitrary coherences `β_f` packaged as
   data, and `G_F`, `g_F` for them.
2. The shape-twisted group for shapes that are general categories rather than preorders.
3. The ordered layer. `IsFormallyReal` already exists separately in `Jordan/`.
