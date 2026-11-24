module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Matrix.Basic

/-!
# Torsion-freeness of the congruence kernel over power series

For a torsion-free commutative ring `R`, a square matrix over `R⟦X⟧` with constant term `1` and
finite order is `1` (`Matrix.eq_one_of_pow_eq_one`). That is, the kernel of
`GL_n(R⟦X⟧) → GL_n(R)` is torsion-free.

Proof: write `M = 1 + D`. If every coefficient of `D` below degree `j` vanishes then `D = Xʲ E`,
and `0 = Mᵏ - 1 = (∑_{i<k} Mⁱ) D` has degree-`j` coefficient `k • E(0)`, since the sum has
constant term `k • 1`. So `E(0) = 0` by torsion-freeness, i.e. the degree-`j` coefficient of `D`
vanishes too.
-/

@[expose] public section

open PowerSeries

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **The congruence kernel over `R⟦X⟧` is torsion-free**: a matrix over `R⟦X⟧` with constant
term `1` and `Mᵏ = 1` for some `k ≠ 0` is `1`, when `R` is torsion-free. -/
theorem eq_one_of_pow_eq_one [IsAddTorsionFree R] (M : Matrix n n R⟦X⟧)
    (h0 : (constantCoeff (R := R)).mapMatrix M = 1) {k : ℕ} (hk : k ≠ 0) (hM : M ^ k = 1) :
    M = 1 := by
  set D := M - 1 with hD
  have hQ : (constantCoeff (R := R)).mapMatrix (∑ i ∈ Finset.range k, M ^ i) =
      k • (1 : Matrix n n R) := by
    rw [map_sum]
    simp only [map_pow, h0, one_pow, Finset.sum_const, Finset.card_range]
  have hstep : ∀ j, (∀ m < j, ∀ a b, coeff m (D a b) = 0) → ∀ a b, coeff j (D a b) = 0 := by
    intro j hj
    have hdvd : ∀ a b, X ^ j ∣ D a b := fun a b => X_pow_dvd_iff.2 fun m hm => hj m hm a b
    choose E hE using hdvd
    have hDE : D = (X ^ j : R⟦X⟧) • Matrix.of E := by
      ext a b
      rw [hE a b]
      rfl
    have hgeom := geom_sum_mul M k
    rw [hM, sub_self, ← hD, hDE, Matrix.mul_smul] at hgeom
    intro a b
    have h1 := congrArg (fun N : Matrix n n R⟦X⟧ => coeff j (N a b)) hgeom
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, map_zero] at h1
    simp only [coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply] at h1
    have h2 : constantCoeff (((∑ i ∈ Finset.range k, M ^ i) * Matrix.of E) a b) =
        k • constantCoeff (E a b) := by
      change (constantCoeff (R := R)).mapMatrix ((∑ i ∈ Finset.range k, M ^ i) * Matrix.of E) a b
        = _
      rw [map_mul, hQ, smul_mul_assoc, one_mul, Matrix.smul_apply]
      rfl
    rw [h2] at h1
    rw [hE a b]
    simp only [coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply]
    exact (nsmul_eq_zero_iff_right hk).mp h1
  have hall : ∀ j a b, coeff j (D a b) = 0 := fun j =>
    Nat.strong_induction_on j fun j ih => hstep j fun m hm => ih m hm
  have hD0 : D = 0 := by
    ext a b j
    rw [hall j a b]
    simp
  rwa [hD, sub_eq_zero] at hD0

end Matrix
