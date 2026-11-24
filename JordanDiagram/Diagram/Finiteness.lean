module

public import JordanDiagram.Diagram.Group
public import JordanDiagram.Algebra.Generation
public import Mathlib.Data.Finite.Perm

/-!
# Detecting configurations

* `card_le_factorial_of_faithful`: the finite detector criterion — a group
  acting faithfully on a finite set `X` embeds in `Perm X`, so `|G| ≤ |X|!`.
* `JordanDiagram.card_autGroup_le`: generating configurations combined with the finite detector
  criterion. If `X ⊆ J` is finite, stable under `G_F(R)`, Jordan-generates `J`, and the terminal
  maps are injective, then `G_F(R)` is finite of order at most `|X|!`. The
  single-algebra input, that an automorphism is determined on a generating set, is
  `jordanAut.ext_of_adjoin_eq_top` in `JordanDiagram/Algebra/Generation.lean`.
-/

@[expose] public section

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

/-- **Finite detector criterion**. -/
theorem card_le_factorial_of_faithful (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    [Finite X] : Finite G ∧ Nat.card G ≤ (Nat.card X).factorial := by
  have hinj : Function.Injective (MulAction.toPermHom G X) := MulAction.toPerm_injective
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  rw [← Nat.card_perm]
  exact Nat.card_le_card_of_injective _ hinj

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I] [TerminallyPointed I]
variable {F : JordanDiagram.{u, v} R I}

/-- The permutation of a `G_F(R)`-stable subset `X ⊆ J` induced by a diagram automorphism. -/
def permOfStable {X : Set F.J} (hX : ∀ g : F.autGroup, ∀ x ∈ X, ev F g x ∈ X) :
    F.autGroup →* Equiv.Perm X where
  toFun g :=
    { toFun := fun x => ⟨ev F g x, hX g x x.2⟩
      invFun := fun x => ⟨ev F g⁻¹ x, hX g⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext <| by
        change ev F g⁻¹ (ev F g x) = x
        rw [map_inv, jordanAut.inv_apply_self]
      right_inv := fun x => Subtype.ext <| by
        change ev F g (ev F g⁻¹ x) = x
        rw [map_inv, jordanAut.apply_inv_self] }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **Generating configurations**, with the bound of the finite detector criterion: a finite,
`G_F(R)`-stable, Jordan-generating subset `X ⊆ J` is a detecting configuration, so `G_F(R)` is
finite of order at most `|X|!`. -/
theorem card_autGroup_le (hν : ∀ i, Function.Injective (F.ν i)) {X : Set F.J} [Finite X]
    (hX : ∀ g : F.autGroup, ∀ x ∈ X, ev F g x ∈ X)
    (hgen : NonUnitalAlgebra.adjoin R X = ⊤) :
    Finite F.autGroup ∧ Nat.card F.autGroup ≤ (Nat.card X).factorial := by
  have hinj : Function.Injective (permOfStable hX) := by
    intro g h hgh
    apply ev_injective hν
    apply jordanAut.ext_of_adjoin_eq_top hgen
    intro x hx
    exact congrArg Subtype.val (Equiv.congr_fun hgh ⟨x, hx⟩)
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  rw [← Nat.card_perm]
  exact Nat.card_le_card_of_injective _ hinj

end JordanDiagram
