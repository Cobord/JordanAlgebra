module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Anisotropic quadratic forms over a locally compact normed field are bounded below

Let `K` be a normed field whose closed balls are compact (e.g. `ℝ` or `ℚ_[p]`) and `A` a square
matrix over `K` whose quadratic form is anisotropic: `vᵀ A v ≠ 0` for `v ≠ 0`. Then
`c ‖v‖² ≤ ‖vᵀ A v‖` for some `c > 0` (`Matrix.exists_pos_mul_norm_sq_le_norm`), for the sup norm.
The constant is the minimum of `‖vᵀ A v‖` on the unit sphere, which is compact; a nonzero `v` is
moved onto the sphere by dividing by a coordinate of maximal norm.
-/

@[expose] public section

open Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] {K : Type*} [NormedField K] [ProperSpace K]

/-- **An anisotropic quadratic form is bounded below by a multiple of `‖v‖²`.** -/
theorem exists_pos_mul_norm_sq_le_norm (A : Matrix ι ι K) (hA : ∀ v, v ≠ 0 → v ⬝ᵥ A *ᵥ v ≠ 0) :
    ∃ c > 0, ∀ v : ι → K, c * ‖v‖ ^ 2 ≤ ‖v ⬝ᵥ A *ᵥ v‖ := by
  classical
  set f : (ι → K) → ℝ := fun v => ‖v ⬝ᵥ A *ᵥ v‖
  have hf : Continuous f :=
    (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).norm
  have hhom : ∀ (r : K) v, (r • v) ⬝ᵥ A *ᵥ (r • v) = r ^ 2 * (v ⬝ᵥ A *ᵥ v) := fun r v => by
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · refine ⟨1, one_pos, fun v => ?_⟩
    rw [Subsingleton.elim v 0, norm_zero]
    simp
  have hne : (Metric.sphere (0 : ι → K) 1).Nonempty := ⟨Pi.single (M := fun _ => K) i₀ 1, by
    rw [mem_sphere_zero_iff_norm]
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_) ?_
    · rcases eq_or_ne j i₀ with rfl | h
      · simp
      · simp [h]
    · simpa using norm_le_pi_norm (Pi.single (M := fun _ => K) i₀ 1) i₀⟩
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → K) 1).exists_isMinOn hne hf.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine ⟨f u, norm_pos_iff.2 (hA u hu0), fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [f]
  obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image (fun j => ‖v j‖) ⟨i₀, Finset.mem_univ _⟩
  have hvi : ‖v‖ = ‖v i‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ j))
    (norm_le_pi_norm v i)
  have hvi0 : v i ≠ 0 := by
    intro h
    apply hv
    rw [← norm_eq_zero, hvi, h, norm_zero]
  have hw : (v i)⁻¹ • v ∈ Metric.sphere (0 : ι → K) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, hvi,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hvi0)]
  have h := hmin hw
  simp only [Set.mem_ofPred_eq] at h
  have hv' : v = v i • ((v i)⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hvi0, one_smul]
  calc f u * ‖v‖ ^ 2 ≤ f ((v i)⁻¹ • v) * ‖v i‖ ^ 2 := by rw [hvi]; gcongr
    _ = f v := by
      simp only [f]
      conv_rhs => rw [hv', hhom, norm_mul, norm_pow]
      ring
