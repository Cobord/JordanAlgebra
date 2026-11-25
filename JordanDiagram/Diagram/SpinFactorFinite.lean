module

public import JordanDiagram.Diagram.SpinFactor
public import JordanDiagram.Algebra.DyadicFinite
public import JordanDiagram.Algebra.OrthogonalFlag

/-!
# Dyadic points of definite spin-factor diagrams

For a spin-factor diagram over `Z[1/2]` on `(V, B, W)` whose top piece `W ⊤` is free with a form
positive over `ℝ` and anisotropic over `ℚ₂`, the diagram group `G_F(Z[1/2])` is finite
(`finite_spinDiagram`): it is the stabilizer of the pieces in `O(W ⊤, B)(Z[1/2])`, which is finite
by `ZHalf.finite_of_form`. For an orthogonal flag `W_j = ⨆_{i ≤ j} Uᵢ`, whose stabilizer is
`∏ⱼ O(Uⱼ, B)`, it suffices that every piece is anisotropic over `ℚ₂` (`finite_stabFlag`), although
their sum need not be.
-/

@[expose] public section

open SpinFactor ZHalf Matrix Module

namespace JordanDiagram

theorem ZHalf.isUnit_two : IsUnit (2 : ZHalf) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (2 : ℤ) (S := ZHalf)

section OrthRep

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
  (B : LinearMap.BilinForm R V) (U : Submodule R V)

/-- `O(U, B|_U)` acting on a submodule `U`. Stated over a general ring, where the two additive
structures of `U` (as a submodule, and through its additive group) are unified by unfolding; over
`Z[1/2]` the unfolding is not available. -/
def orthRep : orthogonalGroup (B.restrict U) →*
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ U U U.addCommMonoid U.addCommMonoid
      U.module U.module :=
  (orthogonalGroup (B.restrict U)).subtype

theorem orthRep_injective : Function.Injective (orthRep B U) := Subtype.val_injective

theorem orthRep_isometry (g : orthogonalGroup (B.restrict U)) (x y : U) :
    B.restrict U (orthRep B U g x) (orthRep B U g y) = B.restrict U x y :=
  g.2 x y

end OrthRep

variable {V : Type} [AddCommGroup V] [Module ZHalf V] (B : LinearMap.BilinForm ZHalf V)
  [Fact B.IsSymm] {I : Type*} [Preorder I] [OrderTop I]

/-- **Definite spin-factor diagrams have finitely many dyadic points** when the form on the top
piece is anisotropic over `ℚ₂`. -/
theorem finite_spinDiagram (W : I →o Submodule ZHalf V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ZHalf (W ⊤)) (hpos : ∀ v, v ≠ 0 → 0 < toRat (B v v))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun i j => ((toRat (B (b i) (b j)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (spinDiagram B W).autGroup := by
  let : Invertible (2 : ZHalf) := ZHalf.isUnit_two.invertible
  have : Module.Free ZHalf (W ⊤) := Module.Free.of_basis b
  -- the type is left to be inferred from `orthRep`: written out over `Z[1/2]` directly, its
  -- instances would take a path that cannot be unfolded to this one
  have := finite_of_form (M := W ⊤) b (ρ := orthRep B (W ⊤)) (orthRep_injective B (W ⊤))
    (B.restrict (W ⊤)) (orthRep_isometry B (W ⊤))
    (fun x hx => hpos x fun h => hx (Submodule.coe_eq_zero.1 h)) h2
  exact Finite.of_equiv _ (spinDiagramAutEquiv B W).symm.toEquiv

omit [Fact B.IsSymm] in
/-- **Orthogonal flags with anisotropic pieces have finitely many dyadic points**: for
`V = ⨁ⱼ Uⱼ` with mutually orthogonal nondegenerate pieces, each free with a form positive over `ℝ`
and anisotropic over `ℚ₂` (no condition on a zero piece, whose basis is empty), the stabilizer in
`O(V, B)(Z[1/2])` of the flag `W_j = ⨆_{i ≤ j} Uᵢ` is finite. -/
theorem finite_stabFlag {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {U : ι → Submodule ZHalf V} (hU : DirectSum.IsInternal U) (hO : PairwiseOrthogonal B U)
    (hN : ∀ i, NondegenerateOn B (U i)) {κ : ι → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)] (b : ∀ j, Basis (κ j) ZHalf (U j))
    (hpos : ∀ v, v ≠ 0 → 0 < toRat (B v v))
    (h2 : ∀ j (v : κ j → ℚ_[2]), v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun k k' => ((toRat (B (b j k) (b j k')) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (stabFlag B U) := by
  have := fun j => finite_of_form (M := U j) (b j) (ρ := orthRep B (U j))
    (orthRep_injective B (U j)) (B.restrict (U j)) (orthRep_isometry B (U j))
    (fun x hx => hpos x fun h => hx (Submodule.coe_eq_zero.1 h)) (h2 j)
  exact Finite.of_equiv _ (stabFlagEquivPi hU hO hN).symm.toEquiv

end JordanDiagram
