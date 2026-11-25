module

public import JordanDiagram.Algebra.Dyadic
public import JordanDiagram.MathlibMissing.PosDefIntegerPoints
public import JordanDiagram.MathlibMissing.AnisotropicBound
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import JordanDiagram.Algebra.SpinFactor

/-!
# Finiteness at `2`: forms positive over `ℝ` and anisotropic over `ℚ₂`

`Z[1/2]` is discrete in `ℝ × ℚ₂`: a dyadic number bounded in both absolute values lies in a finite
set. Consequently, for a rational quadratic form positive on nonzero vectors and anisotropic over
`ℚ₂`, the vectors of `Z[1/2]^ι` with a given value form a finite set (`finite_setOf_zHalf`): the
real bound and the `2`-adic bound (`Matrix.exists_pos_mul_norm_sq_le_norm`) together bound their
coordinates in `2^(-N) ℤ ∩ [-K, K]`.

* `finite_of_form`: **a group acting faithfully on a finite free `Z[1/2]`-module and preserving a
  form positive over `ℝ` and anisotropic over `ℚ₂` is finite** (in a basis, the columns of its
  matrices are such vectors);
* `finite_orthogonalGroup`: in particular `O(V, B)(Z[1/2])` is finite for such a form.

This is the finiteness direction of the criterion "finite exactly when compact at `2`", for groups
preserving a form; the converse rests on the Borel–Harish-Chandra theorem.
-/

@[expose] public section

noncomputable section

open Matrix Module

namespace ZHalf

/-- The inclusion `Z[1/2] → ℚ`. -/
def toRat : ZHalf →+* ℚ :=
  IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom ℚ) (isUnit_iff_ne_zero.2 (by norm_num))

theorem toRat_intCast (z : ℤ) : toRat (z : ZHalf) = z := map_intCast toRat z

/-- Every dyadic number is `z / 2^m`. -/
theorem exists_pow_mul_toRat (x : ZHalf) : ∃ (m : ℕ) (z : ℤ), (2 : ℚ) ^ m * toRat x = z := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (2 : ℤ)) x
  obtain ⟨m, hm⟩ := s.2
  refine ⟨m, z, ?_⟩
  have h := congrArg toRat (IsLocalization.mk'_spec ZHalf z s)
  rw [map_mul, eq_intCast (algebraMap ℤ ZHalf), eq_intCast (algebraMap ℤ ZHalf), toRat_intCast,
    toRat_intCast, ← hm] at h
  push_cast at h
  dsimp only
  rw [← h, mul_comm]

theorem toRat_injective : Function.Injective toRat := by
  refine (injective_iff_map_eq_zero toRat).2 fun x hx => ?_
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (2 : ℤ)) x
  have h := congrArg toRat (IsLocalization.mk'_spec ZHalf z s)
  dsimp only at hx ⊢
  rw [map_mul, hx, zero_mul, eq_intCast (algebraMap ℤ ZHalf), toRat_intCast] at h
  have hz : z = 0 := by exact_mod_cast h.symm
  rw [hz, IsLocalization.mk'_zero]

/-- **`Z[1/2]` is discrete in `ℝ × ℚ₂`, `2`-adic half**: a dyadic number of `2`-adic norm at
most `1` is an integer. -/
theorem exists_int_of_norm_le_one (r : ℚ) (m : ℕ) (z : ℤ) (hz : (2 : ℚ) ^ m * r = z)
    (h : ‖(r : ℚ_[2])‖ ≤ 1) : ∃ t : ℤ, r = t := by
  rw [Padic.eq_padicNorm] at h
  have h' : padicNorm 2 r ≤ 1 := by exact_mod_cast h
  have hdvd : ((2 ^ m : ℕ) : ℤ) ∣ z := by
    rw [padicNorm.dvd_iff_norm_le, ← hz, padicNorm.mul]
    have : padicNorm 2 ((2 : ℚ) ^ m) = (2 : ℚ) ^ (-(m : ℤ)) := by
      have h2v : padicValRat 2 2 = 1 := by simpa using padicValRat.self (p := 2) one_lt_two
      rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ two_ne_zero), padicValRat.pow, h2v, mul_one]
      norm_num
    rw [this]
    have h0 : (0 : ℚ) ≤ 2 ^ (-(m : ℤ)) := zpow_nonneg (by norm_num) _
    calc (2 : ℚ) ^ (-(m : ℤ)) * padicNorm 2 r ≤ (2 : ℚ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left h' h0
      _ = _ := by rw [mul_one]; norm_num
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  have h2 : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2
  rw [hz, ht]
  push_cast
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Finitely many dyadic vectors of a given value**: for a rational quadratic form positive on
nonzero integer vectors and anisotropic over `ℚ₂`, the vectors `w ∈ Z[1/2]^ι` with `wᵀ A w = C`
form a finite set. -/
theorem finite_setOf_zHalf (A : Matrix ι ι ℚ)
    (hA : ∀ w : ι → ℤ, w ≠ 0 → 0 < (fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ fun i => (w i : ℚ))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 → v ⬝ᵥ (A.map ((↑) : ℚ → ℚ_[2])) *ᵥ v ≠ 0) (C : ℚ) :
    {w : ι → ZHalf | (fun i => toRat (w i)) ⬝ᵥ A *ᵥ (fun i => toRat (w i)) = C}.Finite := by
  obtain ⟨c, hc, hcv⟩ := exists_pos_mul_norm_sq_le_norm _ h2
  -- a power of `2` clearing the `2`-adic denominators
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max 1 (‖(C : ℚ_[2])‖ / c)) (by norm_num : (1 : ℝ) < 2)
  have hcast : ∀ q : ι → ℚ, (fun i => (q i : ℚ_[2])) ⬝ᵥ (A.map ((↑) : ℚ → ℚ_[2])) *ᵥ
      (fun i => (q i : ℚ_[2])) = ((q ⬝ᵥ A *ᵥ q : ℚ) : ℚ_[2]) := fun q => by
    simp [dotProduct, mulVec, Rat.cast_sum, Rat.cast_mul]
  have hint : ∀ w : ι → ZHalf, (fun i => toRat (w i)) ⬝ᵥ A *ᵥ (fun i => toRat (w i)) = C →
      ∀ i, ∃ t : ℤ, (2 : ℚ) ^ N * toRat (w i) = t := by
    intro w hw i
    set v : ι → ℚ_[2] := fun i => (toRat (w i) : ℚ_[2])
    have hq : ‖v ⬝ᵥ (A.map ((↑) : ℚ → ℚ_[2])) *ᵥ v‖ = ‖(C : ℚ_[2])‖ := by
      rw [hcast, hw]
    have hvi : ‖v i‖ ≤ max 1 (‖(C : ℚ_[2])‖ / c) := by
      have h1 := norm_le_pi_norm v i
      have h2 : c * ‖v‖ ^ 2 ≤ ‖(C : ℚ_[2])‖ := hq ▸ hcv v
      rcases le_or_gt ‖v‖ 1 with h | h
      · exact le_max_of_le_left (h1.trans h)
      · refine le_max_of_le_right (h1.trans ?_)
        rw [le_div_iff₀ hc]
        have h3 : ‖v‖ ≤ ‖v‖ ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h3 hc.le]
    obtain ⟨m, z, hz⟩ := exists_pow_mul_toRat (w i)
    refine exists_int_of_norm_le_one _ m (2 ^ N * z) (by rw [mul_left_comm, hz]; push_cast; ring) ?_
    have h2n : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using Padic.norm_p (p := 2)
    rw [Rat.cast_mul, norm_mul, Rat.cast_pow, norm_pow, Rat.cast_ofNat, h2n, inv_pow]
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    rw [inv_mul_le_iff₀ h2N, mul_one]
    exact hvi.trans hN.le
  -- the integer vectors obtained have bounded value
  set T : Set (ι → ℤ) :=
    {t | (fun i => (t i : ℚ)) ⬝ᵥ A *ᵥ (fun i => (t i : ℚ)) ≤ 4 ^ N * C}
  have hT : T.Finite := finite_setOf_int_le A hA _
  set f : (ι → ZHalf) → ι → ℚ := fun w i => (2 : ℚ) ^ N * toRat (w i)
  refine Set.Finite.of_finite_image (f := f) ((hT.image fun t i => (t i : ℚ)).subset ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩
    choose t ht using hint w hw
    refine ⟨t, ?_, funext fun i => (ht i).symm⟩
    simp only [T, Set.mem_ofPred_eq]
    have : (fun i => (t i : ℚ)) = (2 : ℚ) ^ N • fun i => toRat (w i) :=
      funext fun i => (ht i).symm
    rw [this, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Set.mem_ofPred_eq] at hw
    rw [hw]
    norm_num [← mul_assoc, ← mul_pow]
  · intro w _ w' _ h
    funext i
    apply toRat_injective
    have := congrFun h i
    simp only [f] at this
    exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) this

section Form

variable {M : Type*} [AddCommMonoid M] [Module ZHalf M]

/-- The Gram matrix of a form in a basis, as a rational matrix. -/
def gramRat (β : LinearMap.BilinForm ZHalf M) (b : Basis ι ZHalf M) : Matrix ι ι ℚ :=
  (LinearMap.BilinForm.toMatrix b β).map toRat

theorem toRat_apply_self (β : LinearMap.BilinForm ZHalf M) (b : Basis ι ZHalf M) (x : M) :
    toRat (β x x) =
      (fun i => toRat (b.repr x i)) ⬝ᵥ gramRat β b *ᵥ fun i => toRat (b.repr x i) := by
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b]
  simp [gramRat, dotProduct, mulVec, map_sum, map_mul]

theorem gramRat_map (β : LinearMap.BilinForm ZHalf M) (b : Basis ι ZHalf M) :
    (gramRat β b).map ((↑) : ℚ → ℚ_[2]) =
      Matrix.of fun i j => ((toRat (β (b i) (b j)) : ℚ) : ℚ_[2]) := by
  ext i j
  simp [gramRat]

/-- **Finiteness at `2` for groups preserving a form**: a group acting faithfully on a finite free
`Z[1/2]`-module and preserving a form `β` with `β(x, x) > 0` for `x ≠ 0` and anisotropic over
`ℚ₂` (in the basis `b`) is finite. -/
theorem finite_of_form (b : Basis ι ZHalf M) {G : Type*} [Group G] {ρ : G →* (M ≃ₗ[ZHalf] M)}
    (hρ : Function.Injective ρ) (β : LinearMap.BilinForm ZHalf M)
    (hinv : ∀ g x y, β (ρ g x) (ρ g y) = β x y) (hpos : ∀ x, x ≠ 0 → 0 < toRat (β x x))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun i j => ((toRat (β (b i) (b j)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite G := by
  rw [← gramRat_map] at h2
  have hA : ∀ w : ι → ℤ, w ≠ 0 →
      0 < (fun i => (w i : ℚ)) ⬝ᵥ gramRat β b *ᵥ fun i => (w i : ℚ) := by
    intro w hw
    set x := b.equivFun.symm fun i => (w i : ZHalf)
    have hrepr : ∀ i, toRat (b.repr x i) = w i := fun i => by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply, toRat_intCast]
    have hx : x ≠ 0 := by
      intro h
      apply hw
      funext i
      have := hrepr i
      rw [h, map_zero, Finsupp.zero_apply, map_zero] at this
      exact_mod_cast this.symm
    have := toRat_apply_self β b x
    simp only [hrepr] at this
    rw [← this]
    exact hpos x hx
  let col : G → ι → ι → ZHalf := fun g j i => b.repr (ρ g (b j)) i
  set S : Set (ι → ι → ZHalf) := Set.pi Set.univ fun j =>
    {w : ι → ZHalf | (fun i => toRat (w i)) ⬝ᵥ gramRat β b *ᵥ (fun i => toRat (w i)) =
      gramRat β b j j}
  have hS : S.Finite := Set.Finite.pi fun j => finite_setOf_zHalf _ hA h2 _
  have hcolS : ∀ g, col g ∈ S := fun g j _ => by
    simp only [Set.mem_ofPred_eq, col]
    rw [← toRat_apply_self, hinv]
    simp [gramRat]
  have hinj : Function.Injective col := by
    intro g h hgh
    apply hρ
    apply LinearEquiv.toLinearMap_injective
    refine b.ext fun j => ?_
    exact b.repr.injective (Finsupp.ext fun i => congrFun (congrFun hgh j) i)
  have := hS.to_subtype
  exact Finite.of_injective (fun g => (⟨col g, hcolS g⟩ : S)) fun g h hgh =>
    hinj (congrArg Subtype.val hgh)

/-- **`O(V, B)(Z[1/2])` is finite** for a form positive over `ℝ` and anisotropic over `ℚ₂`. -/
theorem finite_orthogonalGroup {M : Type*} [AddCommGroup M] [Module ZHalf M]
    (b : Basis ι ZHalf M) (β : LinearMap.BilinForm ZHalf M)
    (hpos : ∀ x, x ≠ 0 → 0 < toRat (β x x))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun i j => ((toRat (β (b i) (b j)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (SpinFactor.orthogonalGroup β) :=
  finite_of_form b (ρ := (SpinFactor.orthogonalGroup β).subtype) Subtype.val_injective β
    (fun g => g.2) hpos h2

end Form

end ZHalf
