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
* `Octonion.innerProduct_eq_sum`: the polar form of the norm is diagonal with the same coefficients.
* `Octonion.bijective_innerProduct_iff`: **nonsingularity**: the polar form identifies `O_R(a, b, c)`
  with its dual exactly when `a`, `b`, `c` are units, via the general criterion
  `LinearMap.bijective_iff_isUnit_of_eq_diag` for diagonal forms.
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

/-- The eight norm coefficients are all units exactly when `a`, `b`, `c` are. -/
theorem isUnit_normCoeff_iff : (∀ i, IsUnit (normCoeff a b c i)) ↔ IsUnit a ∧ IsUnit b ∧ IsUnit c := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [normCoeff] using h 1
    · simpa [normCoeff] using h 2
    · simpa [normCoeff] using h 4
  · rintro ⟨ha, hb, hc⟩ i
    fin_cases i <;> simp [normCoeff, IsUnit.mul_iff, ha, hb, hc]

/-- The standard coordinates, as a linear isomorphism `O_R(a, b, c) ≃ R⁸`. -/
def coordsEquiv : Octonion R a b c ≃ₗ[R] (Fin 8 → R) where
  toFun := coords
  invFun v := mk ⟨v 0, v 1, v 2, v 3⟩ ⟨v 4, v 5, v 6, v 7⟩
  map_add' x y := by
    ext i
    fin_cases i <;> rfl
  map_smul' r x := by
    ext i
    fin_cases i <;> rfl
  left_inv x := rfl
  right_inv v := by
    ext i
    fin_cases i <;> rfl

theorem coordsEquiv_apply (x : Octonion R a b c) : coordsEquiv x = coords x := rfl

/-- **The polar form of the norm is diagonal** with the same coefficients:
`⟨x, y⟩ = ∑ᵢ (normCoeff a b c)ᵢ xᵢ yᵢ`. -/
theorem innerProduct_eq_sum [Invertible (2 : R)] [StarRing R] [TrivialStar R]
    (x y : Octonion R a b (-c)) :
    innerProduct x y = ∑ i, normCoeff a b c i * coords x i * coords y i := by
  have hpol := mul_star_add_star_mul_eq_scalarEmbed x y
  have hsum : (x + y) * star (x + y) = x * star x + y * star y + (x * star y + y * star x) := by
    rw [star_add, mul_add, add_mul, add_mul]
    abel
  rw [hpol, mul_star_self_eq_diag, mul_star_self_eq_diag, mul_star_self_eq_diag, ← map_add,
    ← map_add] at hsum
  have key := scalarEmbed_injective hsum
  have hc : ∀ i, coords (x + y) i = coords x i + coords y i := fun i => by
    rw [← coordsEquiv_apply, map_add]
    rfl
  simp only [hc] at key
  have h2 : (2 : R) * innerProduct x y = 2 * ∑ i, normCoeff a b c i * coords x i * coords y i := by
    have : ∑ i, normCoeff a b c i * (coords x i + coords y i) ^ 2 =
        ∑ i, normCoeff a b c i * coords x i ^ 2 + ∑ i, normCoeff a b c i * coords y i ^ 2 +
          2 * ∑ i, normCoeff a b c i * coords x i * coords y i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this] at key
    exact (add_left_cancel key).symm
  have := congrArg (⅟(2 : R) * ·) h2
  simpa only [← mul_assoc, invOf_mul_self, one_mul] using this

end Octonion

namespace LinearMap

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- A bilinear form that is diagonal, with entries `d`, in some coordinates `e : M ≃ R^ι` is
nonsingular (`x ↦ B(x, ·)` is a bijection `M → M*`) exactly when every `dᵢ` is a unit. -/
theorem bijective_iff_isUnit_of_eq_diag (B : M →ₗ[R] M →ₗ[R] R) (e : M ≃ₗ[R] (ι → R))
    (d : ι → R) (hB : ∀ x y, B x y = ∑ i, d i * e x i * e y i) :
    Function.Bijective B ↔ ∀ i, IsUnit (d i) := by
  have hv : ∀ x j, B x (e.symm (Pi.single j 1)) = d j * e x j := fun x j => by
    rw [hB, LinearEquiv.apply_symm_apply]
    simp [Pi.single_apply]
  constructor
  · intro h j
    obtain ⟨x, hx⟩ := h.2 ((LinearMap.proj j).comp e.symm.symm.toLinearMap)
    have := hv x j
    rw [hx] at this
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, LinearMap.coe_proj, Function.eval, Pi.single_eq_same] at this
    exact IsUnit.of_mul_eq_one (e x j) this.symm
  · intro hd
    refine ⟨(injective_iff_map_eq_zero B).2 fun x hx => ?_, fun f => ?_⟩
    · apply e.injective
      ext j
      have := hv x j
      rw [hx, LinearMap.zero_apply] at this
      rw [map_zero, Pi.zero_apply]
      exact ((hd j).mul_right_eq_zero).1 this.symm
    · refine ⟨e.symm fun j => ↑(hd j).unit⁻¹ * f (e.symm (Pi.single j 1)), ?_⟩
      refine ((Pi.basisFun R ι).map e.symm).ext fun j => ?_
      rw [Module.Basis.map_apply, Pi.basisFun_apply, hv, LinearEquiv.apply_symm_apply, ← mul_assoc,
        IsUnit.mul_val_inv, one_mul]

end LinearMap

namespace Octonion

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R] {a b c : R}

/-- **Nonsingularity of the norm**: the polar form of the norm of `O_R(a, b, c)` identifies the
module with its dual exactly when `a`, `b`, `c` are units of `R`. -/
theorem bijective_innerProduct_iff :
    Function.Bijective (innerProduct : LinearMap.BilinForm R (Octonion R a b (-c))) ↔
      IsUnit a ∧ IsUnit b ∧ IsUnit c := by
  rw [LinearMap.bijective_iff_isUnit_of_eq_diag _ coordsEquiv (normCoeff a b c)
    fun x y => innerProduct_eq_sum x y, isUnit_normCoeff_iff]

end Octonion
