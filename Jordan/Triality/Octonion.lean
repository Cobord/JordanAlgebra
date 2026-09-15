import Jordan.Octonion
import Jordan.Triality.DivisionAlgebra
import Jordan.Triality.Gauged

/-!
# The octonion triality

Over a commutative ring `R` with `2` invertible and trivial `star`, write `𝕆` for
`Octonion R a b c` (in prose only; the code spells it out). Suppose the norm form of `𝕆` is
*anisotropic* in the strong sense that `x * star x` is a unit for every
`x ≠ 0` (true for Cayley's octonions over a field where a sum of eight squares vanishes only
trivially, e.g. usual octonions over `ℝ`), and that the polarized norm form `innerProduct`
identifies `𝕆` with its dual (automatic over a field, by dimension count, once it is injective;
over a general ring it amounts to `a`, `b`, `c` being units). Then:

* `Octonion.divisionAlgebra`: the octonions are a `DivisionAlgebra R`. Left multiplication by `x`
  is undone, up to the scalar `x * star x`, by left multiplication by `star x`
  (`star_mul_mul_eq_center`), and similarly on the right.
* `Octonion.triality`: `t x y z := ⟨x * y, z⟩` is a `Triality R 𝕆 𝕆 𝕆`. Each perfect-pairing
  axiom is "`innerProduct` identifies `𝕆` with its dual" composed with one of the multiplication
  bijections, after moving factors across the inner product with
  `innerProduct_mul_left`/`innerProduct_mul_right`.
* `Octonion.ofM1_mul`: choosing `e₁ = e₂ = 1`, the division algebra `DivAlg₁₂` that the triality
  cuts out of `𝕆ᵛ` is `𝕆` itself, the identification `x ↦ ⟨x, ·⟩` being multiplicative.
* `Octonion.normedTriality`: for `R` a `StarOrderedRing` on which the norm form is nonnegative,
  `innerProduct` makes this a `NormedTriality`: the bound `⟨xy, z⟩² ≤ ‖x‖² ‖y‖² ‖z‖²` is
  Cauchy–Schwarz plus `‖xy‖² = ‖x‖² ‖y‖²`, and it is attained at `z = xy`, `y = x̄ z`, `x = z ȳ`.
-/

open scoped Quaternion

namespace Octonion

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R] {a b c : R}

omit [Invertible (2 : R)] [StarRing R] [TrivialStar R] in
instance [Nontrivial R] : Nontrivial (Octonion R a b c) :=
  inferInstanceAs (Nontrivial (ℍ[R, a, 0, b] × ℍ[R, a, 0, b]))

section TrilinearForm

/-! ### The trilinear form `t x y z = ⟨x * y, z⟩` -/

theorem innerProduct_self (x : Octonion R a b c) : innerProduct x x = (x * star x).1.re := by
  rw [innerProduct_apply]
  show ⅟(2 : R) * ((x * star x).1.re + (x * star x).1.re) = _
  rw [← two_mul, ← mul_assoc, invOf_mul_self, one_mul]

theorem innerProduct_flip :
    (innerProduct : LinearMap.BilinForm R (Octonion R a b c)).flip = innerProduct :=
  LinearMap.ext fun x => LinearMap.ext fun y => innerProduct_comm y x

/-- The octonion trilinear form `t x y z = ⟨x * y, z⟩`. -/
noncomputable def trialityForm :
    Octonion R a b c →ₗ[R] Octonion R a b c →ₗ[R] Module.Dual R (Octonion R a b c) :=
  (LinearMap.mul R (Octonion R a b c)).compr₂ innerProduct

@[simp] theorem trialityForm_apply (x y : Octonion R a b c) :
    trialityForm (R := R) (a := a) (b := b) (c := c) x y = innerProduct (x * y) := rfl

omit [Invertible (2 : R)] [StarRing R] [TrivialStar R] in
private theorem star_ne_zero' {x : Octonion R a b c} (hx : x ≠ 0) : star x ≠ 0 :=
  fun h => hx (star_eq_zero.mp h)

end TrilinearForm

section Anisotropic

/-! ### Under anisotropy of the norm form

`hN`: every nonzero octonion has unit norm. -/

variable (hN : ∀ x : Octonion R a b c, x ≠ 0 → IsUnit (x * star x).1.re)
include hN

section DivisionAlgebra

/-- Left multiplication by a nonzero octonion is bijective: `star x * (x * y) = N x • y`. -/
theorem mulLeft_bijective {x : Octonion R a b c} (hx : x ≠ 0) : Function.Bijective (x * ·) := by
  have hn := hN x hx
  constructor
  · intro y y' h
    have h' := congrArg (star x * ·) h
    simp only [star_mul_mul_eq_center, ← re_mul_star_self] at h'
    have := congrArg ((↑hn.unit⁻¹ : R) • ·) h'
    simpa only [smul_smul, IsUnit.val_inv_mul, one_smul] using this
  · intro z
    refine ⟨(↑hn.unit⁻¹ : R) • (star x * z), ?_⟩
    show x * ((↑hn.unit⁻¹ : R) • (star x * z)) = z
    rw [mul_smul_comm, mul_star_mul_eq_center, ← re_mul_star_self, smul_smul, IsUnit.val_inv_mul,
      one_smul]

/-- Right multiplication by a nonzero octonion is bijective: `(u * y) * star y = N y • u`. -/
theorem mulRight_bijective {y : Octonion R a b c} (hy : y ≠ 0) : Function.Bijective (· * y) := by
  have hn := hN y hy
  constructor
  · intro u u' h
    have h' := congrArg (· * star y) h
    simp only [mul_mul_star_eq_center, ← re_mul_star_self] at h'
    have := congrArg ((↑hn.unit⁻¹ : R) • ·) h'
    simpa only [smul_smul, IsUnit.val_inv_mul, one_smul] using this
  · intro z
    refine ⟨(↑hn.unit⁻¹ : R) • (z * star y), ?_⟩
    show ((↑hn.unit⁻¹ : R) • (z * star y)) * y = z
    rw [smul_mul_assoc, mul_star_mul_eq'_center, ← re_mul_star_self, smul_smul, IsUnit.val_inv_mul,
      one_smul]

/-- With anisotropic norm form, the octonions are a (non-associative) division algebra. -/
abbrev divisionAlgebra [Nontrivial R] : DivisionAlgebra R (Octonion R a b c) :=
  DivisionAlgebra.ofBijective (fun hx => mulLeft_bijective hN hx)
    (fun hy => mulRight_bijective hN hy)

end DivisionAlgebra

section DualPairing

/-! ### The inner product identifies `𝕆` with its dual -/

variable [Nontrivial R]

/-- Anisotropy makes `x ↦ ⟨x, ·⟩` injective: `⟨x, ·⟩ = 0` forces `N x = ⟨x, x⟩ = 0`. -/
theorem innerProduct_injective :
    Function.Injective (innerProduct : Octonion R a b c →ₗ[R] Module.Dual R (Octonion R a b c)) :=
  (injective_iff_map_eq_zero _).mpr fun x hx => by
    by_contra h
    have h0 := innerProduct_self x
    rw [hx, LinearMap.zero_apply] at h0
    have hu := hN x h
    rw [← h0] at hu
    exact not_isUnit_zero hu

end DualPairing

section Attainment

/-! ### Attaining `⟨x y, z⟩² = ‖x‖² ‖y‖² ‖z‖²`

Writing `‖x‖² = ⟨x, x⟩`, the identity `‖x y‖² = ‖x‖² ‖y‖²` (`innerProduct_mul_mul_star`) gives
equality at `z = x y`; and `x (x̄ z) = ‖x‖² z`, `(z ȳ) y = ‖y‖² z` give it at `y = x̄ z` and
`x = z ȳ`. No order on `R` is involved. -/

theorem innerProduct_isUnit_self {z : Octonion R a b c} (hz : z ≠ 0) :
    IsUnit (innerProduct z z) := by
  rw [innerProduct_self]; exact hN z hz

theorem eq_zero_or_eq_zero_of_mul_eq_zero {x y : Octonion R a b c} (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr ((mulLeft_bijective hN hx).1 (show x * y = x * 0 by rw [h, mul_zero]))

/-- Attained in `z`: at `z = x y`, both sides are `(‖x‖² ‖y‖²)²`. -/
theorem exists_normSq_innerProduct_mul_eq_z [Nontrivial R] (x y : Octonion R a b c) :
    ∃ z, z ≠ 0 ∧ innerProduct (x * y) z * innerProduct (x * y) z =
      innerProduct x x * innerProduct y y * innerProduct z z := by
  by_cases h : x * y = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [h, map_zero, LinearMap.zero_apply, mul_zero]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hN h with rfl | rfl <;> simp
  · refine ⟨x * y, h, ?_⟩
    rw [innerProduct_mul_mul_star x y x, ← innerProduct_self y]
    ring

/-- Attained in `y`: at `y = x̄ z`, `x y = ‖x‖² z`, so both sides are `(‖x‖² ‖z‖²)²`. -/
theorem exists_normSq_innerProduct_mul_eq_y [Nontrivial R] (x z : Octonion R a b c) :
    ∃ y, y ≠ 0 ∧ innerProduct (x * y) z * innerProduct (x * y) z =
      innerProduct x x * innerProduct y y * innerProduct z z := by
  by_cases hx : x = 0
  · exact ⟨1, one_ne_zero, by subst hx; simp⟩
  by_cases hz : z = 0
  · exact ⟨1, one_ne_zero, by subst hz; simp⟩
  refine ⟨star x * z, fun h => hz ((mulLeft_bijective hN (star_ne_zero' hx)).1
    (show star x * z = star x * 0 by rw [h, mul_zero])), ?_⟩
  rw [mul_star_mul_eq_center, ← re_mul_star_self, ← innerProduct_self x, map_smul,
    LinearMap.smul_apply, smul_eq_mul, innerProduct_mul_mul_star_left z (star x) z, star_star,
    ← innerProduct_self x]
  ring

/-- Attained in `x`: at `x = z ȳ`, `x y = ‖y‖² z`, so both sides are `(‖y‖² ‖z‖²)²`. -/
theorem exists_normSq_innerProduct_mul_eq_x [Nontrivial R] (y z : Octonion R a b c) :
    ∃ x, x ≠ 0 ∧ innerProduct (x * y) z * innerProduct (x * y) z =
      innerProduct x x * innerProduct y y * innerProduct z z := by
  by_cases hy : y = 0
  · exact ⟨1, one_ne_zero, by subst hy; simp⟩
  by_cases hz : z = 0
  · exact ⟨1, one_ne_zero, by subst hz; simp⟩
  refine ⟨z * star y, fun h => hz ((mulRight_bijective hN (star_ne_zero' hy)).1
    (show z * star y = 0 * star y by rw [h, zero_mul])), ?_⟩
  rw [mul_star_mul_eq'_center, ← re_mul_star_self, ← innerProduct_self y, map_smul,
    LinearMap.smul_apply, smul_eq_mul, innerProduct_mul_mul_star z (star y) z, star_star,
    re_star_mul_self, innerProduct_self y, re_mul_star_self]
  ring

end Attainment

section InnerForm

/-! ### The inner product as an `InnerProductForm`

For `R` partially ordered with the norm form nonnegative, `hpos`, the polarized norm form
`innerProduct` is a positive definite inner product on `𝕆`: definiteness is anisotropy `hN`
again. When moreover `R` is a `StarOrderedRing` (with its trivial star, the nonnegative cone is
generated by the squares), Cauchy–Schwarz and `‖x y‖² = ‖x‖² ‖y‖²` give the bound
`⟨x y, z⟩² ≤ ‖x‖² ‖y‖² ‖z‖²`. -/

variable [Nontrivial R] [PartialOrder R] (hpos : ∀ x : Octonion R a b c, 0 ≤ (x * star x).1.re)
include hpos

/-- `innerProduct` as a (trivially-)sesquilinear positive definite form. -/
noncomputable def innerForm : InnerProductForm R (Octonion R a b c) where
  toLinearMap := Triality.linearEquivStarSemilinear innerProduct
  posSemidef :=
    { isSymm := ⟨fun u z => by
        simp only [Triality.linearEquivStarSemilinear_apply, starRingEnd_apply, star_trivial]
        exact innerProduct_comm u z⟩
      isNonneg := ⟨fun w => by
        rw [Triality.linearEquivStarSemilinear_apply, innerProduct_self]
        exact hpos w⟩ }
  definite w hw := by
    rw [Triality.linearEquivStarSemilinear_apply, innerProduct_self] at hw
    by_contra h
    exact not_isUnit_zero (hw ▸ hN w h)

@[simp] theorem innerForm_apply (u z : Octonion R a b c) :
    innerForm hN hpos u z = innerProduct u z := rfl

omit [Nontrivial R] in
/-- The bound `⟨x y, z⟩² ≤ ‖x‖² ‖y‖² ‖z‖²`: Cauchy–Schwarz for `u = x y` and
`‖x y‖² = ‖y‖² ‖x‖²` (`innerProduct_mul_mul_star`). -/
theorem normSq_innerProduct_mul_le [StarOrderedRing R] (x y z : Octonion R a b c) :
    innerProduct (x * y) z * innerProduct (x * y) z ≤
      innerProduct x x * innerProduct y y * innerProduct z z := by
  by_cases hz : z = 0
  · subst hz; simp
  · refine (cauchySchwarz_of_isUnit innerProduct innerProduct_comm
      (fun w => by rw [innerProduct_self]; exact hpos w) (innerProduct_isUnit_self hN hz)).trans
      (le_of_eq ?_)
    rw [innerProduct_mul_mul_star x y x, ← innerProduct_self y]
    ring

end InnerForm

section PerfectPairing

/-! ### Under perfectness of the polarized norm form

`hP`: `x ↦ ⟨x, ·⟩` is onto `𝕆ᵛ`. Over a field this follows from `innerProduct_injective` by
dimension count; over a general ring it is a hypothesis. -/

variable [Nontrivial R]
  (hP : Function.Surjective (innerProduct : Octonion R a b c →ₗ[R] Module.Dual R (Octonion R a b c)))
include hP

theorem innerProduct_bijective :
    Function.Bijective (innerProduct : Octonion R a b c →ₗ[R] Module.Dual R (Octonion R a b c)) :=
  ⟨innerProduct_injective hN, hP⟩

theorem innerProduct_flip_bijective :
    Function.Bijective ((innerProduct : LinearMap.BilinForm R (Octonion R a b c)).flip) := by
  rw [innerProduct_flip]; exact innerProduct_bijective hN hP

section Triality

/-! ### The triality -/

/-- The octonion triality `t x y z = ⟨x * y, z⟩`. -/
noncomputable abbrev triality :
    Triality R (Octonion R a b c) (Octonion R a b c) (Octonion R a b c) :=
  Triality.ofTrivialStar trialityForm
    -- `y ↦ ⟨x*y, ·⟩ = innerProduct ∘ (x * ·)`
    (fun x hx => (innerProduct_bijective hN hP).comp (mulLeft_bijective hN hx))
    -- `z ↦ ⟨x*·, z⟩ = ⟨·, star x * z⟩ = innerProduct.flip ∘ (star x * ·)`
    (fun x hx => by
      have : ⇑(trialityForm x).flip =
          ⇑(innerProduct : LinearMap.BilinForm R (Octonion R a b c)).flip ∘ (star x * ·) := by
        funext z; ext y
        simp only [LinearMap.flip_apply, trialityForm_apply, Function.comp_apply,
          innerProduct_mul_left]
      rw [this]
      exact (innerProduct_flip_bijective hN hP).comp (mulLeft_bijective hN (star_ne_zero' hx)))
    -- `x ↦ ⟨x*y, ·⟩ = innerProduct ∘ (· * y)`
    (fun y hy => (innerProduct_bijective hN hP).comp (mulRight_bijective hN hy))
    -- `z ↦ ⟨·*y, z⟩ = ⟨·, z * star y⟩ = innerProduct.flip ∘ (· * star y)`
    (fun y hy => by
      have : ⇑(trialityForm.flip y).flip =
          ⇑(innerProduct : LinearMap.BilinForm R (Octonion R a b c)).flip ∘ (· * star y) := by
        funext z; ext x
        simp only [LinearMap.flip_apply, trialityForm_apply, Function.comp_apply,
          innerProduct_mul_right]
      rw [this]
      exact (innerProduct_flip_bijective hN hP).comp (mulRight_bijective hN (star_ne_zero' hy)))
    -- `x ↦ ⟨x*·, z⟩ = ⟨·, star x * z⟩ = innerProduct.flip ∘ (· * z) ∘ star`
    (fun z hz => by
      have : (fun x : Octonion R a b c => (trialityForm x).flip z) =
          ⇑(innerProduct : LinearMap.BilinForm R (Octonion R a b c)).flip ∘ (· * z) ∘ star := by
        funext x; ext y
        simp only [LinearMap.flip_apply, trialityForm_apply, Function.comp_apply,
          innerProduct_mul_left]
      rw [this]
      exact (innerProduct_flip_bijective hN hP).comp
        ((mulRight_bijective hN hz).comp star_involutive.bijective))
    -- `y ↦ ⟨·*y, z⟩ = ⟨·, z * star y⟩ = innerProduct.flip ∘ (z * ·) ∘ star`
    (fun z hz => by
      have : (fun y : Octonion R a b c => (trialityForm.flip y).flip z) =
          ⇑(innerProduct : LinearMap.BilinForm R (Octonion R a b c)).flip ∘ (z * ·) ∘ star := by
        funext y; ext x
        simp only [LinearMap.flip_apply, trialityForm_apply, Function.comp_apply,
          innerProduct_mul_right]
      rw [this]
      exact (innerProduct_flip_bijective hN hP).comp
        ((mulLeft_bijective hN hz).comp star_involutive.bijective))

@[simp] theorem triality_prod_apply (x y : Octonion R a b c) :
    (triality hN hP).triality_prod x y = innerProduct (x * y) := rfl

end Triality

section Recover

/-! ### Recovering `𝕆` from its triality

Choosing both distinguished elements to be `1`, each of the three division algebras
`DivAlg₁₂`, `DivAlg₁₃`, `DivAlg₂₃` cut out of a dual of `𝕆` is `𝕆` itself. The two identifications
always differ by `star` (or coincide), and exactly one of them is multiplicative: `ofM1` for
`DivAlg₁₂`, `ofM3` for `DivAlg₁₃`, `ofM2` for `DivAlg₂₃`. The isomorphisms are packaged as `≃+*`
(the repo's convention for isomorphisms of non-associative algebras, cf. `OctonionMatrix`), with
`R`-linearity as a separate `_smul` lemma since the underlying maps are (semi)linear equivs. -/

section DivAlg₁₂

open Triality.DivAlg₁₂

/-- Both identifications `𝕆 ≃ 𝕆ᵛ` of `DivAlg₁₂` are `x ↦ ⟨x, ·⟩`. -/
theorem divAlg₁₂_ofM1_eq_ofM2 (x : Octonion R a b c) :
    ofM1 (triality hN hP) one_ne_zero one_ne_zero x =
      ofM2 (triality hN hP) one_ne_zero one_ne_zero x := by
  rw [ofM1_apply, ofM2_apply, triality_prod_apply, triality_prod_apply, mul_one, one_mul]

theorem divAlg₁₂_ofM1_mul (x y : Octonion R a b c) :
    ofM1 (triality hN hP) one_ne_zero one_ne_zero (x * y) =
      ofM1 (triality hN hP) one_ne_zero one_ne_zero x *
        ofM1 (triality hN hP) one_ne_zero one_ne_zero y := by
  rw [divAlg₁₂_ofM1_eq_ofM2 hN hP y, ofM1_mul_ofM2, ofM1_apply, triality_prod_apply,
    triality_prod_apply, mul_one]

/-- `𝕆 ≃ DivAlg₁₂` as `R`-algebras, via `x ↦ ⟨x, ·⟩`. -/
noncomputable def equivDivAlg₁₂ :
    Octonion R a b c ≃+* (triality hN hP).DivAlg₁₂ one_ne_zero one_ne_zero :=
  { ofM1 (triality hN hP) one_ne_zero one_ne_zero with
    map_mul' := divAlg₁₂_ofM1_mul hN hP }

@[simp] theorem equivDivAlg₁₂_apply (x : Octonion R a b c) :
    equivDivAlg₁₂ hN hP x = ofM1 (triality hN hP) one_ne_zero one_ne_zero x :=
  rfl

theorem equivDivAlg₁₂_smul (r : R) (x : Octonion R a b c) :
    equivDivAlg₁₂ hN hP (r • x) = r • equivDivAlg₁₂ hN hP x :=
  map_smul (ofM1 (triality hN hP) one_ne_zero one_ne_zero) r x

end DivAlg₁₂

section DivAlg₁₃

open Triality.DivAlg₁₃

/-- The identifications `𝕆 ≃ M̄𝕆ᵛ` of `DivAlg₁₃` are `x ↦ ⟨x·, 1⟩ = ⟨·, star x⟩` and
`z ↦ ⟨·, z⟩`, so they differ by `star`. -/
theorem divAlg₁₃_ofM1_eq_ofM3_star (x : Octonion R a b c) :
    ofM1 (triality hN hP) one_ne_zero one_ne_zero x =
      ofM3 (triality hN hP) one_ne_zero one_ne_zero (star x) := by
  rw [ofM1_apply, ofM3_apply]
  apply LinearMap.ext; intro y
  simp only [Triality.triality_prod_xz_apply, triality_prod_apply, innerProduct_mul_left,
    one_mul, mul_one]

theorem divAlg₁₃_ofM3_mul (z z' : Octonion R a b c) :
    ofM3 (triality hN hP) one_ne_zero one_ne_zero (z * z') =
      ofM3 (triality hN hP) one_ne_zero one_ne_zero z *
        ofM3 (triality hN hP) one_ne_zero one_ne_zero z' := by
  rw [show ofM3 (triality hN hP) one_ne_zero one_ne_zero z =
      ofM1 (triality hN hP) one_ne_zero one_ne_zero (star z) from by
    rw [divAlg₁₃_ofM1_eq_ofM3_star, star_star]]
  rw [ofM1_mul_ofM3, ofM3_apply]
  apply LinearMap.ext; intro y
  simp only [Triality.triality_prod_xz_apply, triality_prod_apply, innerProduct_mul_left,
    one_mul, star_star]

/-- `𝕆 ≃ DivAlg₁₃` as `R`-algebras, via `z ↦ ⟨·, z⟩`. -/
noncomputable def equivDivAlg₁₃ :
    Octonion R a b c ≃+* (triality hN hP).DivAlg₁₃ one_ne_zero one_ne_zero :=
  { ofM3 (triality hN hP) one_ne_zero one_ne_zero with
    map_mul' := divAlg₁₃_ofM3_mul hN hP }

@[simp] theorem equivDivAlg₁₃_apply (z : Octonion R a b c) :
    equivDivAlg₁₃ hN hP z = ofM3 (triality hN hP) one_ne_zero one_ne_zero z :=
  rfl

theorem equivDivAlg₁₃_smul (r : R) (z : Octonion R a b c) :
    equivDivAlg₁₃ hN hP (r • z) = r • equivDivAlg₁₃ hN hP z :=
  map_smul (ofM3 (triality hN hP) one_ne_zero one_ne_zero) r z

end DivAlg₁₃

section DivAlg₂₃

open Triality.DivAlg₂₃

/-- The identifications `𝕆 ≃ 𝕆ᵛ` of `DivAlg₂₃` are `y ↦ ⟨·y, 1⟩ = ⟨·, star y⟩` and `z ↦ ⟨·, z⟩`,
so they differ by `star`. -/
theorem divAlg₂₃_ofM2_eq_ofM3_star (y : Octonion R a b c) :
    ofM2 (triality hN hP) one_ne_zero one_ne_zero y =
      ofM3 (triality hN hP) one_ne_zero one_ne_zero (star y) := by
  rw [ofM2_apply, ofM3_apply]
  apply LinearMap.ext; intro x
  simp only [Triality.triality_prod_yz_apply, triality_prod_apply, innerProduct_mul_right,
    one_mul, mul_one]

/-- `ofM3` is *anti*-multiplicative here (`⟨·, z z'⟩ = ofM3 z' * ofM3 z`); it is the
`star`-twisted `ofM2` that is multiplicative. -/
theorem divAlg₂₃_ofM2_mul (y y' : Octonion R a b c) :
    ofM2 (triality hN hP) one_ne_zero one_ne_zero (y * y') =
      ofM2 (triality hN hP) one_ne_zero one_ne_zero y *
        ofM2 (triality hN hP) one_ne_zero one_ne_zero y' := by
  rw [divAlg₂₃_ofM2_eq_ofM3_star hN hP y', ofM2_mul_ofM3, ofM2_apply]
  apply LinearMap.ext; intro x
  simp only [Triality.triality_prod_yz_apply, triality_prod_apply, innerProduct_mul_right,
    one_mul, star_mul]

/-- `𝕆 ≃ DivAlg₂₃` as `R`-algebras, via `y ↦ ⟨·, star y⟩`. -/
noncomputable def equivDivAlg₂₃ :
    Octonion R a b c ≃+* (triality hN hP).DivAlg₂₃ one_ne_zero one_ne_zero :=
  { ofM2 (triality hN hP) one_ne_zero one_ne_zero with
    map_mul' := divAlg₂₃_ofM2_mul hN hP }

@[simp] theorem equivDivAlg₂₃_apply (y : Octonion R a b c) :
    equivDivAlg₂₃ hN hP y = ofM2 (triality hN hP) one_ne_zero one_ne_zero y :=
  rfl

/-- `ofM2` is `starRingEnd R`-semilinear, which with trivial `star` is plain linearity. -/
theorem equivDivAlg₂₃_smul (r : R) (y : Octonion R a b c) :
    equivDivAlg₂₃ hN hP (r • y) = r • equivDivAlg₂₃ hN hP y := by
  rw [equivDivAlg₂₃_apply, equivDivAlg₂₃_apply, map_smulₛₗ, starRingEnd_apply, star_trivial]

end DivAlg₂₃

end Recover

section Normed

/-! ### The octonion triality is a normed triality -/

variable [PartialOrder R] [StarOrderedRing R] (hpos : ∀ x : Octonion R a b c, 0 ≤ (x * star x).1.re)
include hpos

/-- With `innerProduct` as inner product on all three slots, the octonion triality is a
`NormedTriality`: `⟨x y, z⟩² ≤ ‖x‖² ‖y‖² ‖z‖²`, attained in each slot. -/
noncomputable abbrev normedTriality :
    NormedTriality R (Octonion R a b c) (Octonion R a b c) (Octonion R a b c) :=
  { triality hN hP with
    inner_x := innerForm hN hpos
    inner_y := innerForm hN hpos
    inner_z := innerForm hN hpos
    normSq_triality_prod_le := fun x y z => by
      show star (innerProduct (x * y) z) * innerProduct (x * y) z ≤
        innerProduct x x * innerProduct y y * innerProduct z z
      rw [star_trivial]
      exact normSq_innerProduct_mul_le hN hpos x y z
    exists_normSq_triality_prod_eq_z := fun x y => by
      obtain ⟨z, hz, h⟩ := exists_normSq_innerProduct_mul_eq_z hN x y
      exact ⟨z, hz, by rw [star_trivial]; exact h⟩
    exists_normSq_triality_prod_eq_y := fun x z => by
      obtain ⟨y, hy, h⟩ := exists_normSq_innerProduct_mul_eq_y hN x z
      exact ⟨y, hy, by rw [star_trivial]; exact h⟩
    exists_normSq_triality_prod_eq_x := fun y z => by
      obtain ⟨x, hx, h⟩ := exists_normSq_innerProduct_mul_eq_x hN y z
      exact ⟨x, hx, by rw [star_trivial]; exact h⟩ }

omit hpos in
/-- The sign conditions `a ≤ 0`, `b ≤ 0`, `0 ≤ c` on the Cayley–Dickson parameters (see the sign
convention in `Jordan.Octonion`) make the norm form nonnegative (`norm_nonneg_of_signs`), so they
replace the positivity hypothesis of `normedTriality`. -/
noncomputable abbrev normedTrialityOfSigns (ha : a ≤ 0) (hb : b ≤ 0) (hc : 0 ≤ c) :
    NormedTriality R (Octonion R a b c) (Octonion R a b c) (Octonion R a b c) :=
  normedTriality hN hP (norm_nonneg_of_signs ha hb hc)

end Normed

end PerfectPairing

end Anisotropic

end Octonion
