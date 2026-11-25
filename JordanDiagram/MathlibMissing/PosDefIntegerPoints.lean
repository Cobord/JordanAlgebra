module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Round

/-!
# Integer vectors of bounded value under a positive rational quadratic form

Let `A` be a square rational matrix with `wᵀ A w > 0` for every nonzero integer vector `w`. Then
for every bound `C` there are only finitely many integer vectors `w` with `wᵀ A w ≤ C`
(`Matrix.finite_setOf_int_le`). The proof passes to `ℝ`: the form stays positive on nonzero real
vectors (a real zero would be a kernel vector of `A + Aᵀ`, hence give a rational kernel vector
by the determinant), so by compactness of the unit sphere it is at least `c ‖v‖²` with `c > 0`,
which bounds the coordinates of the integer vectors in question.
-/

@[expose] public section

open Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- A quadratic form, nonnegative on a vector space over an ordered field, vanishes at `v` only if
the polarization `A + Aᵀ` kills `v`. -/
theorem add_transpose_mulVec_eq_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix ι ι K) (hA : ∀ v, 0 ≤ v ⬝ᵥ A *ᵥ v) {v : ι → K} (hv : v ⬝ᵥ A *ᵥ v = 0) :
    (A + Aᵀ) *ᵥ v = 0 := by
  set B := A + Aᵀ
  have hsymm : ∀ u w : ι → K, u ⬝ᵥ B *ᵥ w = w ⬝ᵥ B *ᵥ u := fun u w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, transpose_add, transpose_transpose,
      add_comm]
  have hB : ∀ u, u ⬝ᵥ B *ᵥ u = 2 * (u ⬝ᵥ A *ᵥ u) := fun u => by
    rw [add_mulVec, dotProduct_add, two_mul, mulVec_transpose, dotProduct_comm u (u ᵥ* A),
      ← dotProduct_mulVec]
  set u := B *ᵥ v
  have hexp : ∀ t : K, (v + t • u) ⬝ᵥ B *ᵥ (v + t • u) =
      2 * t * (u ⬝ᵥ B *ᵥ v) + t ^ 2 * (u ⬝ᵥ B *ᵥ u) := fun t => by
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [hsymm v u, hB v, hv]
    ring
  have hnn : ∀ t : K, 0 ≤ 2 * t * (u ⬝ᵥ B *ᵥ v) + t ^ 2 * (u ⬝ᵥ B *ᵥ u) := fun t => by
    rw [← hexp, hB]
    exact mul_nonneg zero_le_two (hA _)
  have hb : u ⬝ᵥ B *ᵥ v = 0 := by
    have ha : 0 ≤ u ⬝ᵥ B *ᵥ u := by rw [hB]; exact mul_nonneg zero_le_two (hA _)
    set a := u ⬝ᵥ B *ᵥ u
    set b := u ⬝ᵥ B *ᵥ v
    by_contra hb
    have h := hnn (-b / (a + 1))
    have ha1 : 0 < a + 1 := by linarith
    have hb2 : 0 < b ^ 2 := by positivity
    have : 2 * (-b / (a + 1)) * b + (-b / (a + 1)) ^ 2 * a =
        -(b ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
      field_simp
      ring
    rw [this] at h
    have : 0 < b ^ 2 * (a + 2) / (a + 1) ^ 2 := by positivity
    rw [neg_div] at h
    linarith
  exact dotProduct_self_eq_zero.1 hb

/-- A real quadratic form positive on nonzero vectors is at least `c ‖v‖²` for some `c > 0`. -/
theorem exists_pos_mul_norm_sq_le (A : Matrix ι ι ℝ) (hA : ∀ v ≠ 0, 0 < v ⬝ᵥ A *ᵥ v) :
    ∃ c > 0, ∀ v : ι → ℝ, c * ‖v‖ ^ 2 ≤ v ⬝ᵥ A *ᵥ v := by
  set f : (ι → ℝ) → ℝ := fun v => v ⬝ᵥ A *ᵥ v
  have hf : Continuous f := continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hhom : ∀ (r : ℝ) v, f (r • v) = r ^ 2 * f v := fun r v => by
    simp only [f, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun v => ?_⟩
    rw [Subsingleton.elim v 0, norm_zero]
    simp
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hf.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine ⟨f u, hA u hu0, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [f]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h := hmin hw
  simp only [Set.mem_ofPred_eq] at h
  calc f u * ‖v‖ ^ 2 ≤ f (‖v‖⁻¹ • v) * ‖v‖ ^ 2 := by gcongr
    _ = f v := by
      rw [hhom, mul_comm, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne', one_pow, one_mul]

/-- A rational quadratic form positive on nonzero integer vectors is positive on nonzero real
vectors. -/
theorem pos_of_pos_int [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hA : ∀ w : ι → ℤ, w ≠ 0 → 0 < (fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ fun i => (w i : ℚ))
    (v : ι → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (A.map ((↑) : ℚ → ℝ)) *ᵥ v := by
  set A' := A.map ((↑) : ℚ → ℝ)
  -- positivity on nonzero rational vectors, by clearing denominators
  have hQ : ∀ q : ι → ℚ, q ≠ 0 → 0 < q ⬝ᵥ A *ᵥ q := by
    intro q hq
    set N : ℕ := ∏ i, (q i).den
    have hN : (N : ℚ) ≠ 0 := by
      simp only [N, Nat.cast_prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (q i).den_nz
    have hint : ∀ i, ∃ z : ℤ, (N : ℚ) * q i = z := fun i => by
      obtain ⟨k, hk⟩ : (q i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨k * (q i).num, ?_⟩
      rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, mul_comm ((q i).den : ℚ),
        mul_assoc, Rat.den_mul_eq_num]
    choose w hw using hint
    have hwq : (fun i => (w i : ℚ)) = (N : ℚ) • q := funext fun i => (hw i).symm
    have hw0 : w ≠ 0 := by
      intro h
      apply hq
      funext i
      have := hw i
      rw [h, Pi.zero_apply, Int.cast_zero, mul_eq_zero] at this
      exact this.resolve_left hN
    have h := hA w hw0
    rw [hwq, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
    have hN0 : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    exact pos_of_mul_pos_right (pos_of_mul_pos_right h hN0) hN0
  -- nonnegativity over `ℝ`, by density of rational vectors
  have hdense : DenseRange fun q : ι → ℚ => fun i => (q i : ℝ) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hcast : ∀ q : ι → ℚ, (fun i => (q i : ℝ)) ⬝ᵥ A' *ᵥ (fun i => (q i : ℝ)) =
      ((q ⬝ᵥ A *ᵥ q : ℚ) : ℝ) := fun q => by
    simp [A', dotProduct, mulVec, Rat.cast_sum, Rat.cast_mul]
  have hnn : ∀ u : ι → ℝ, 0 ≤ u ⬝ᵥ A' *ᵥ u := fun u =>
    hdense.induction_on (p := fun u => 0 ≤ u ⬝ᵥ A' *ᵥ u) u
      (isClosed_le continuous_const
        (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))
      fun q => by
        rw [hcast]
        rcases eq_or_ne q 0 with rfl | hq
        · simp
        · exact_mod_cast (hQ q hq).le
  -- a real zero would give a rational kernel vector of `A + Aᵀ`
  refine (hnn v).lt_of_ne fun h0 => ?_
  have hker := add_transpose_mulVec_eq_zero A' hnn h0.symm
  have hdet : (A + Aᵀ).det = 0 := by
    have : (A' + A'ᵀ).det = 0 := (exists_mulVec_eq_zero_iff).1 ⟨v, hv, hker⟩
    have hmap : A' + A'ᵀ = (Rat.castHom ℝ).mapMatrix (A + Aᵀ) := by
      ext i j
      simp [A']
    rw [hmap, ← RingHom.map_det] at this
    simpa using this
  obtain ⟨q, hq, hBq⟩ := (exists_mulVec_eq_zero_iff).2 hdet
  have h2 : q ⬝ᵥ (A + Aᵀ) *ᵥ q = 2 * (q ⬝ᵥ A *ᵥ q) := by
    rw [add_mulVec, dotProduct_add, two_mul, mulVec_transpose, dotProduct_comm q (q ᵥ* A),
      ← dotProduct_mulVec]
  have := hQ q hq
  rw [hBq, dotProduct_zero] at h2
  linarith

/-- **Finitely many integer vectors of bounded value**: for a rational quadratic form positive on
nonzero integer vectors, `{w ∈ ℤ^ι : wᵀ A w ≤ C}` is finite. -/
theorem finite_setOf_int_le [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hA : ∀ w : ι → ℤ, w ≠ 0 → 0 < (fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ fun i => (w i : ℚ)) (C : ℚ) :
    {w : ι → ℤ | (fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ (fun i => (w i : ℚ)) ≤ C}.Finite := by
  set A' := A.map ((↑) : ℚ → ℝ)
  obtain ⟨c, hc, hcv⟩ := exists_pos_mul_norm_sq_le A' (pos_of_pos_int A hA)
  set K : ℤ := ⌈(C : ℝ) / c⌉
  refine (Set.Finite.pi (t := fun _ => Set.Icc (-K) K) fun _ => Set.finite_Icc _ _).subset ?_
  intro w hw i _
  have hw' : (fun i => (w i : ℝ)) ⬝ᵥ A' *ᵥ (fun i => (w i : ℝ)) ≤ C := by
    have : (fun i => (w i : ℝ)) ⬝ᵥ A' *ᵥ (fun i => (w i : ℝ)) =
        (((fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ (fun i => (w i : ℚ)) : ℚ) : ℝ) := by
      simp [A', dotProduct, mulVec, Rat.cast_sum, Rat.cast_mul]
    rw [this]
    exact_mod_cast hw
  have hi : |(w i : ℝ)| ≤ ‖fun i => (w i : ℝ)‖ := by
    have := norm_le_pi_norm (fun i => (w i : ℝ)) i
    rwa [Real.norm_eq_abs] at this
  have hsq : (w i : ℝ) ^ 2 ≤ C / c := by
    rw [le_div_iff₀ hc, ← sq_abs]
    have h3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hi 2) hc.le
    linarith [hcv (fun i => (w i : ℝ))]
  have habs : |w i| ≤ K := by
    have h1 : (|w i| : ℤ) ≤ w i ^ 2 := by
      rw [← sq_abs]
      rcases (abs_nonneg (w i)).eq_or_lt with h | h
      · rw [← h]; simp
      · nlinarith
    have h2 : ((w i ^ 2 : ℤ) : ℝ) ≤ C / c := by push_cast; exact hsq
    exact h1.trans (Int.cast_le.1 (h2.trans (Int.le_ceil _)))
  exact abs_le.1 habs
