module

public import JordanDiagram.Algebra.Automorphism

/-!
# Automorphisms `1 + e D` for a square-zero scalar `e`

Let `M` be a Jordan algebra over a commutative ring `T`, `D` a Jordan derivation of `M`, and
`e ∈ T` with `e² = 0`. Then `x ↦ x + e D(x)` is a Jordan automorphism of `M`, with inverse
`x ↦ x - e D(x)`: multiplicativity is the Leibniz rule, the term `e² D(x) D(y)` vanishing.

* `sqZeroAut e he D`: this automorphism, written `1 + e D`.
* `sqZeroAut_add`: `(1 + e D)(1 + e D') = 1 + e (D + D')`.
* `sqZeroAut_commutator`: for `e² = e'² = 0`, the group commutator of `1 + e D` and `1 + e' D'` is
  `1 + e e' [D, D']`.
-/

@[expose] public section

namespace JordanAlgebra

variable {T : Type*} [CommRing T] {M : Type*} [JordanAlgebra T M]

/-- The linear map `1 + e D`. -/
def sqZeroLin (e : T) (D : JordanDerivation T M) : M →ₗ[T] M :=
  LinearMap.id + e • (D : M →ₗ[T] M)

theorem sqZeroLin_apply (e : T) (D : JordanDerivation T M) (x : M) :
    sqZeroLin e D x = x + e • D x := rfl

theorem sqZeroLin_comp_apply (e e' : T) (D D' : JordanDerivation T M) (x : M) :
    sqZeroLin e D (sqZeroLin e' D' x) = x + e • D x + e' • D' x + (e * e') • D (D' x) := by
  rw [sqZeroLin_apply, sqZeroLin_apply, map_add, JordanDerivation.map_smul, smul_add, smul_smul]
  abel

theorem sqZeroLin_neg_comp (e : T) (he : e * e = 0) (D : JordanDerivation T M) :
    sqZeroLin e D ∘ₗ sqZeroLin (-e) D = LinearMap.id := by
  ext x
  rw [LinearMap.comp_apply, sqZeroLin_comp_apply, mul_neg, he, neg_zero, zero_smul, add_zero,
    neg_smul, add_neg_cancel_right, LinearMap.id_apply]

theorem sqZeroLin_map_mul (e : T) (he : e * e = 0) (D : JordanDerivation T M) (x y : M) :
    sqZeroLin e D (x * y) = sqZeroLin e D x * sqZeroLin e D y := by
  rw [sqZeroLin_apply, sqZeroLin_apply, sqZeroLin_apply, D.leibniz, add_mul, mul_add, mul_add,
    smul_mul_smul_comm, he, zero_smul, add_zero, mul_smul_comm, smul_mul_assoc, smul_add]
  abel

/-- The Jordan automorphism `1 + e D` of `M`, for `e² = 0` and a derivation `D`. -/
def sqZeroAut (e : T) (he : e * e = 0) (D : JordanDerivation T M) : jordanAut T M :=
  ⟨LinearEquiv.ofLinearMap (sqZeroLin e D) (sqZeroLin (-e) D) (sqZeroLin_neg_comp e he D)
      (by simpa only [neg_neg] using sqZeroLin_neg_comp (-e) (by rw [neg_mul_neg, he]) D),
    sqZeroLin_map_mul e he D⟩

@[simp]
theorem sqZeroAut_apply (e : T) (he : e * e = 0) (D : JordanDerivation T M) (x : M) :
    sqZeroAut e he D x = x + e • D x := rfl

/-- `(1 + e D)(1 + e D') = 1 + e (D + D')`. -/
theorem sqZeroAut_add (e : T) (he : e * e = 0) (D D' : JordanDerivation T M) :
    sqZeroAut e he (D + D') = sqZeroAut e he D * sqZeroAut e he D' := by
  refine jordanAut.ext fun x => ?_
  rw [jordanAut.mul_apply, sqZeroAut_apply, sqZeroAut_apply, sqZeroAut_apply,
    JordanDerivation.add_apply, map_add, JordanDerivation.map_smul, smul_add, smul_add, smul_smul,
    he, zero_smul, add_zero]
  abel

theorem sqZeroAut_zero (e : T) (he : e * e = 0) : sqZeroAut e he (0 : JordanDerivation T M) = 1 :=
  jordanAut.ext fun x => by
    rw [sqZeroAut_apply, JordanDerivation.zero_apply, smul_zero, add_zero, jordanAut.one_apply]

/-- `(1 + e D)⁻¹ = 1 - e D`. -/
theorem sqZeroAut_neg (e : T) (he : e * e = 0) (D : JordanDerivation T M) :
    sqZeroAut e he (-D) = (sqZeroAut e he D)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← sqZeroAut_add, neg_add_cancel, sqZeroAut_zero]

/-- **Commutators**: for `e² = e'² = 0`, the group commutator of `1 + e D` and `1 + e' D'` is
`1 + e e' [D, D']`. -/
theorem sqZeroAut_commutator (e e' : T) (he : e * e = 0) (he' : e' * e' = 0)
    (D D' : JordanDerivation T M) :
    sqZeroAut e he D * sqZeroAut e' he' D' * (sqZeroAut e he D)⁻¹ * (sqZeroAut e' he' D')⁻¹ =
      sqZeroAut (e * e') (by rw [mul_mul_mul_comm, he, zero_mul]) ⁅D, D'⁆ := by
  rw [← sqZeroAut_neg, ← sqZeroAut_neg]
  refine jordanAut.ext fun x => ?_
  simp only [jordanAut.mul_apply, sqZeroAut_apply, JordanDerivation.lie_apply,
    JordanDerivation.neg_apply, map_add, map_neg, JordanDerivation.map_smul, smul_neg, smul_sub,
    smul_smul]
  have h₃ : e * (e * e') = 0 := by rw [← mul_assoc, he, zero_mul]
  have h₄ : e' * (e * e') = 0 := by rw [mul_left_comm, he', mul_zero]
  simp only [he, he', h₃, h₄, mul_zero, zero_smul, add_zero, mul_comm e' e]
  abel

end JordanAlgebra
