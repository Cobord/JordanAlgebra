module

public import Jordan.Octonion

/-!
# The norm coefficients of the generalized octonions

Write `O_R(a, b, c)` for the Cayley–Dickson algebra obtained by doubling three times with
generators squaring to `a`, `b`, `c`. In `Jordan/Octonion.lean` this is `Octonion R a b (-c)`:
it doubles `ℍ[R, a, 0, b]` with norm `N(p, q) = N_H(p) - c N_H(q)`.

* `Octonion.mul_star_self_eq_diag`: **the norm is diagonal** in the standard basis
  `1, i, j, k, ℓ, iℓ, jℓ, kℓ`, with coefficients `1, -a, -b, ab, -c, ac, bc, -abc`: the coefficient
  of the basis element indexed by `S ⊆ {a, b, c}` is `∏_{γ ∈ S} (-γ)`.
* `Octonion.normCoeff_pos`: over an ordered ring, these coefficients are all positive when
  `a, b, c < 0`.
-/

@[expose] public section

open scoped Quaternion

namespace Octonion

variable {R : Type*} [CommRing R] {a b c : R}

/-- The quaternion norm `N_H(q) = q₀² - a q₁² - b q₂² + ab q₃²` on `ℍ[R, a, 0, b]`. -/
theorem star_mul_self_re (q : ℍ[R, a, 0, b]) :
    (star q * q).re = q.re ^ 2 - a * q.imI ^ 2 - b * q.imJ ^ 2 + a * b * q.imK ^ 2 := by
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-- The eight norm coefficients `1, -a, -b, ab, -c, ac, bc, -abc` of `O_R(a, b, c)`. -/
def normCoeff (a b c : R) : Fin 8 → R :=
  ![1, -a, -b, a * b, -c, a * c, b * c, -(a * b * c)]

/-- The eight coordinates of an octonion in the standard basis. -/
def coords (x : Octonion R a b c) : Fin 8 → R :=
  ![x.1.re, x.1.imI, x.1.imJ, x.1.imK, x.2.re, x.2.imI, x.2.imJ, x.2.imK]

/-- **The norm of `O_R(a, b, c)` is diagonal** with coefficients `1, -a, -b, ab, -c, ac, bc, -abc`:
`x x̄ = ∑ᵢ (normCoeff a b c)ᵢ xᵢ²`. -/
theorem mul_star_self_eq_diag [StarRing R] [TrivialStar R] (x : Octonion R a b (-c)) :
    x * star x = scalarEmbed (∑ i, normCoeff a b c i * coords x i ^ 2) := by
  rw [mul_star_self_eq_scalarEmbed, star_mul_self_re, star_mul_self_re]
  congr 1
  simp only [Fin.sum_univ_eight]
  simp [normCoeff, coords]
  ring

/-- Over an ordered ring with `a, b, c < 0`, all eight norm coefficients are positive. -/
theorem normCoeff_pos [LinearOrder R] [IsStrictOrderedRing R] (ha : a < 0) (hb : b < 0)
    (hc : c < 0) (i : Fin 8) : 0 < normCoeff a b c i := by
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  fin_cases i <;> simp [normCoeff]
  · exact ha
  · exact hb
  · exact hab
  · exact hc
  · exact mul_pos_of_neg_of_neg ha hc
  · exact mul_pos_of_neg_of_neg hb hc
  · exact mul_neg_of_pos_of_neg hab hc

end Octonion
