# JordanDiagram

Formalization of *Symmetries of Jordan Algebra Diagrams over Varying Base Rings* (the paper whose
earlier draft is in [`Beyond/`](../Beyond/)), built on the `Jordan` library. It follows the order
suggested in Remark B.4 of the paper. Scalar extension is done for one base map `R → S` at a time
(`F ↦ S ⊗[R] F`). The coherent family `{F_R}` with its isomorphisms `β_f`, and functoriality in
the base map, are not yet formalized.

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

The library has two parts:

* [`Algebra/`](Algebra/) concerns the symmetries of a single Jordan algebra, either generic or
  one of the algebras already formalized in `Jordan/`. Nothing in it mentions diagrams.
* [`Diagram/`](Diagram/) is the new content: terminally pointed diagrams, their automorphism
  groups and compatible derivations, and statements about them.

### `Algebra/`: symmetries of one algebra

| File | Paper | Contents |
| --- | --- | --- |
| [`Automorphism.lean`](Algebra/Automorphism.lean) | Def. 2.3 | `jordanAut R A`, setwise stabilizers `jordanAut.stab`, and lifting along an injective homomorphism: an automorphism or derivation of `J` that preserves `range ν` transports to `A` (`liftAut`, `liftDer`). |
| [`Equiv.lean`](Algebra/Equiv.lean) | Def. 2.3 | `JordanEquiv` (`A ≃ⱼ[R] B`) with `refl`, `symm`, `trans`. `JordanEquiv.lift`: an isomorphism `J ≃ⱼ J'` carrying `range ν` onto `range ν'` lifts along injective `ν`, `ν'`. |
| [`Generation.lean`](Algebra/Generation.lean) | input to Lemma 4.3 | `jordanAut.ext_of_adjoin_eq_top`: an automorphism is determined by its values on a generating set. |
| [`BaseChange.lean`](Algebra/BaseChange.lean) | Lemma 2.4 | With `2` invertible in `R`, `S ⊗[R] A` is a Jordan `S`-algebra (`instJordanAlgebra`). The proof goes through the fully linearized identity `lin`, which is multilinear, and `jordanExpr_add`. Also scalar extension of morphisms (`baseChangeHom`, injective for flat `S`), of automorphisms (`baseChangeAut`) and of derivations (`baseChangeDer`). |
| [`SpinFactor.lean`](Algebra/SpinFactor.lean) | Def. 5.2; Lemma 5.5 | For `V`, `V'` free, `2` invertible and any symmetric forms, including degenerate ones: `isometryEquiv : Isometry B B' ≃ (J(V, B) ≃ⱼ J(V', B'))` (`g ↦ g ⊕ id`), `autEquivOrthogonal : O(V, B)(R) ≃* Aut J(V, B)`, and `derEquivSkew : o(V, B)(R) ≃ Der J(V, B)` (`X ↦ X ⊕ 0`). |

### `Diagram/`: the diagram layer

| File | Paper | Contents |
| --- | --- | --- |
| [`Basic.lean`](Diagram/Basic.lean) | Defs. 2.5, 2.8 | `TerminallyPointed`, `JordanDiagram`, restriction along a functor, the terminal algebra `J`, the terminal maps `ν i` and the terminal relation `ν_map`, and the images `Aᵢ`. |
| [`Group.lean`](Diagram/Group.lean) | Defs. 3.1, 3.4; Prop. 3.6; Lemma 3.11 | The diagram automorphism group `autGroup`, terminal evaluation `ev`, and terminal determination: `ev_injective`, `range_ev`, and `autGroupEquivStab : G_F(R) ≃* ⋂ᵢ Stab(Aᵢ)`. Also `restrictHom`. |
| [`Derivation.lean`](Diagram/Derivation.lean) | Def. 3.7; Prop. 3.8; Lemma 3.11 | A componentwise Lie algebra structure on Pi types, which Mathlib lacks. The compatible derivations `derAlgebra` as a Lie subalgebra, the Lie homomorphism `evDer`, `evDer_injective`, `range_evDer` (image `{D : D(Aᵢ) ⊆ Aᵢ}`), and `restrictDer`. |
| [`Wedge.lean`](Diagram/Wedge.lean) | Prop. 3.12 | `IsWedge P₁ P₂` and `autGroupEquivWedge : G_F(R) ≃* G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)`. For derivations, `wedgeDer_injective` and `range_wedgeDer`. |
| [`Iso.lean`](Diagram/Iso.lean) | Prop. 2.7 (fibers); Def. 3.13; Prop. 3.14 | `DiagramIso F F'` and its terminal determination `terminalEquiv` (isomorphisms `↔` `h : J ≃ⱼ J'` with `h(Aᵢ) = A'ᵢ`). `TwistedIso F u = DiagramIso F (u* F)`. `twistedIdEquiv` identifies the twisted isomorphisms over `𝟭` with `G_F(R)`, the kernel in Prop. 3.14. `twistedTerminalEquiv` is the terminal description in Prop. 3.14. |
| [`Finiteness.lean`](Diagram/Finiteness.lean) | Prop. 4.2; Lemma 4.3 | The finite detector criterion: a faithful action on a finite `X` gives `\|G\| ≤ \|X\|!`. `card_autGroup_le`: a finite, stable, Jordan-generating `X ⊆ J` bounds `\|G_F(R)\|` by `\|X\|!`. |
| [`SpinFactor.lean`](Diagram/SpinFactor.lean) | Def. 5.3; Lemma 5.4; Props. 5.6, 5.7 | `spinDiagram B W` for monotone `W : I →o Submodule R V`. Its terminal maps are injective, with image `R 1 ⊕ Wᵢ`. `spinDiagramAutEquiv : G_F(R) ≃* Stab_{O(W ⊤, B)}(W)`, `spinDiagramDerEquiv : g_F(R) ≃ Stab_{o(W ⊤, B)}(W)`, and `spinDiagramIsoEquiv`: isomorphisms of spin-factor diagrams are isometries of the configurations. |
| [`BaseChange.lean`](Diagram/BaseChange.lean) | Lemma 2.11; Props. 3.3, 7.9(b) | `F.baseChange S = S ⊗[R] F`. `autBaseChange : G_F(R) →* G_F(S)`, injective when every `F(i) → S ⊗ F(i)` is (`autBaseChange_injective`). `derBaseChange` on compatible derivations, additive and bracket-preserving. Terminal maps stay injective along flat `R → S`. |

Build with `lake build JordanDiagram`. The default target is still the `jordan` executable. There
are no `sorry`s. The headline results use only `propext`, `Classical.choice` and `Quot.sound`.

## Next steps

1. Functoriality in the base: the coherence isomorphisms `T ⊗_S (S ⊗_R F) ≅ T ⊗_R F` as Jordan
   isomorphisms, giving `G_F : CAlg_R → Grp` (Prop. 3.3) and the families of Def. 2.8.
   Prop. 7.9(c), the image of `G_F(R) → G_F(E)` for finite free nodes.
2. Spin-factor flags: Corollary 5.10 (orthogonal decomposition, `G_F ≅ ∏ O(Uⱼ)`) and the wreath
   product of Example 5.9.
3. The group structure on all of `G̃_F(R)`, with `u` ranging over `Aut(I⁺, +)`.
4. The ordered layer (Section 6). `IsFormallyReal` already exists separately in `Jordan/`.
