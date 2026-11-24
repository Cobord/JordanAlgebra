import Mathlib.Algebra.Lie.Basic

/-!
# Lie rings and Lie algebras on Pi types

Mathlib has no Lie ring structure on a product `∀ i, L i` of Lie rings. This file provides the
componentwise one (`Pi.instLieRing`, `Pi.instLieAlgebra`, `Pi.lie_apply`). It is used for the
compatible derivations `g_F(R) ⊆ ∀ i, Der(F(i))` of a diagram (Definition 3.7), and is generic.
-/

variable {ι : Type*} {L : ι → Type*}

/-- The componentwise Lie ring structure on a product of Lie rings. -/
instance Pi.instLieRing [∀ i, LieRing (L i)] : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie _ _ _ := funext fun _ => add_lie _ _ _
  lie_add _ _ _ := funext fun _ => lie_add _ _ _
  lie_self _ := funext fun _ => lie_self _
  leibniz_lie _ _ _ := funext fun _ => leibniz_lie _ _ _

theorem Pi.lie_apply [∀ i, LieRing (L i)] (x y : ∀ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ := rfl

/-- The componentwise Lie algebra structure on a product of Lie algebras. -/
instance Pi.instLieAlgebra (R : Type*) [CommRing R] [∀ i, LieRing (L i)]
    [∀ i, LieAlgebra R (L i)] : LieAlgebra R (∀ i, L i) where
  lie_smul _ _ _ := funext fun _ => lie_smul _ _ _
