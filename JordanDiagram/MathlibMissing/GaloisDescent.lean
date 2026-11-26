module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Group.End

/-!
# Galois descent for vector spaces

Let `L/k` be a finite Galois extension with group `Gal(L/k)`.

* `exists_tmul_of_forall_rTensor_eq`: an element of `L ⊗[k] M` fixed by every `σ ⊗ 1` is `1 ⊗ m`.
* **Speiser's lemma.** Let `V` be an `L`-vector space with a semilinear action `ρ` of `Gal(L/k)`
  (`ρ σ (c • v) = σ c • ρ σ v`). Then the fixed vectors `V^ρ` (`fixedPoints ρ`, a `k`-subspace)
  satisfy `L ⊗[k] V^ρ ≅ V` by `c ⊗ v ↦ c • v` (`bijective_liftBaseChange_fixedPoints`): fixed
  vectors that are independent over `k` are independent over `L` (`linearIndependent_of_fixed`),
  and the fixed vectors span `V` over `L` (`span_fixedPoints`). Spanning uses Dedekind's
  independence of characters: the vectors `(σ a)_σ`, `a ∈ L`, span `L^{Gal(L/k)}`
  (`span_range_galoisVector`).
-/

@[expose] public section

noncomputable section

open TensorProduct Module

namespace GaloisDescent

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]

section Tensor

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- **Invariants of `L ⊗[k] M`**: an element fixed by every `σ ⊗ 1` is `1 ⊗ m`. -/
theorem exists_tmul_of_forall_rTensor_eq (x : L ⊗[k] M)
    (hx : ∀ σ : L ≃ₐ[k] L, LinearMap.rTensor M (σ : L →ₐ[k] L).toLinearMap x = x) :
    ∃ m : M, x = (1 : L) ⊗ₜ m := by
  classical
  set b := Basis.ofVectorSpace k M
  set B := b.baseChange L
  have hrepr : ∀ (σ : L ≃ₐ[k] L) (y : L ⊗[k] M) i,
      B.repr (LinearMap.rTensor M (σ : L →ₐ[k] L).toLinearMap y) i = σ (B.repr y i) := by
    intro σ y i
    induction y with
    | add y z hy hz => rw [map_add, map_add, Finsupp.add_apply, hy, hz, map_add,
        Finsupp.add_apply, map_add]
    | tmul a m =>
      rw [LinearMap.rTensor_tmul, Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
        AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, map_smul]
  have hfix : ∀ i, ∀ σ : L ≃ₐ[k] L, σ (B.repr x i) = B.repr x i := fun i σ => by
    rw [← hrepr, hx]
  choose c hc using fun i => (IsGalois.mem_range_algebraMap_iff_fixed (F := k) _).2 (hfix i)
  have hfin : (Function.support c).Finite := (B.repr x).support.finite_toSet.subset fun i hi => by
    simp only [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff] at hi ⊢
    rw [← hc i]
    exact fun h => hi ((algebraMap k L).injective (h.trans (map_zero _).symm))
  refine ⟨b.repr.symm (Finsupp.ofSupportFinite c hfin), B.repr.injective (Finsupp.ext fun i => ?_)⟩
  rw [Basis.baseChange_repr_tmul, LinearEquiv.apply_symm_apply, Finsupp.ofSupportFinite_coe,
    ← hc i, Algebra.smul_def, mul_one]

end Tensor

section Speiser

variable {V : Type*} [AddCommGroup V] [Module L V] [Module k V] [IsScalarTower k L V]
variable (ρ : (L ≃ₐ[k] L) → V →+ V)

/-- The vectors fixed by the action, a `k`-subspace. -/
def fixedPoints (hρ : ∀ σ (c : L) v, ρ σ (c • v) = σ c • ρ σ v) : Submodule k V where
  carrier := {v | ∀ σ, ρ σ v = v}
  add_mem' {v w} hv hw σ := by rw [map_add, hv, hw]
  zero_mem' σ := map_zero _
  smul_mem' c v hv σ := by
    rw [← algebraMap_smul L c v, hρ, hv, AlgEquiv.commutes]

omit [FiniteDimensional k L] [IsGalois k L] in
theorem mem_fixedPoints (hρ : ∀ σ (c : L) v, ρ σ (c • v) = σ c • ρ σ v) {v : V} :
    v ∈ fixedPoints ρ hρ ↔ ∀ σ, ρ σ v = v := Iff.rfl

omit [IsGalois k L] in
/-- **Dedekind**: the vectors `(σ a)_σ`, `a ∈ L`, span `L^{Gal(L/k)}` over `L`. -/
theorem span_range_galoisVector :
    Submodule.span L (Set.range fun a : L => fun σ : L ≃ₐ[k] L => σ a) = ⊤ := by
  classical
  by_contra h
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
  apply hf
  have hfa : ∀ a : L, ∑ σ : L ≃ₐ[k] L, f (Pi.single σ 1) * σ a = 0 := fun a => by
    have h0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.mem_ker] at h0
    have hsum : (fun σ : L ≃ₐ[k] L => σ a) = ∑ σ, σ a • Pi.single σ (1 : L) :=
      funext fun τ => by simp [Finset.sum_apply, Pi.single_apply]
    have := h0
    simp only [hsum, map_sum, map_smul, smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun σ _ => mul_comm _ _
  have hinj : Function.Injective fun σ : L ≃ₐ[k] L => (σ : L →* L) := fun σ τ h =>
    AlgEquiv.ext fun a => DFunLike.congr_fun h a
  have hli := (linearIndependent_monoidHom L L).comp _ hinj
  have hc : ∀ σ : L ≃ₐ[k] L, f (Pi.single σ 1) = 0 :=
    Fintype.linearIndependent_iff.1 hli _ (funext fun a => by simpa using hfa a)
  refine LinearMap.pi_ext fun σ x => ?_
  rw [show (Pi.single σ x : (L ≃ₐ[k] L) → L) = x • Pi.single σ 1 by
    ext τ; by_cases h : τ = σ <;> simp [h],
    map_smul, hc, smul_zero, LinearMap.zero_apply]

variable (hρ : ∀ σ (c : L) v, ρ σ (c • v) = σ c • ρ σ v)
include hρ

omit [IsGalois k L] in
/-- **Speiser's lemma, spanning**: the fixed vectors of an action (`ρ 1 = id`,
`ρ (σ τ) = ρ σ ∘ ρ τ`) span `V` over `L`. -/
theorem span_fixedPoints (hone : ∀ v, ρ 1 v = v) (hmul : ∀ σ τ v, ρ (σ * τ) v = ρ σ (ρ τ v)) :
    Submodule.span L (fixedPoints ρ hρ : Set V) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun v => ?_
  set ψ : ((L ≃ₐ[k] L) → L) →ₗ[L] V := Fintype.linearCombination L fun σ => ρ σ v
  have h1 : ψ (Pi.single 1 1) = v := by
    simp [ψ, Fintype.linearCombination_apply, Pi.single_apply, hone]
  have hmap : ∀ a : L, ψ (fun σ => σ a) ∈ fixedPoints ρ hρ := by
    intro a τ
    simp only [ψ, Fintype.linearCombination_apply, map_sum, hρ]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [AlgEquiv.mul_apply, hmul]
  have hmem : (Pi.single 1 1 : (L ≃ₐ[k] L) → L) ∈
      Submodule.span L (Set.range fun a : L => fun σ : L ≃ₐ[k] L => σ a) := by
    rw [span_range_galoisVector]
    exact Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := ψ) hmem
  rw [Submodule.map_span, h1] at this
  refine Submodule.span_mono ?_ this
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact hmap a

/-- **Speiser's lemma, independence**: fixed vectors independent over `k` are independent over
`L`. -/
theorem linearIndependent_of_fixed {ι : Type*} (v : ι → V) (hfix : ∀ σ i, ρ σ (v i) = v i)
    (hv : LinearIndependent k v) : LinearIndependent L v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg i₀ hi₀
  by_contra hne
  set g' : ι → L := fun i => (g i₀)⁻¹ * g i
  have hg' : ∑ i ∈ s, g' i • v i = 0 := by
    simp only [g', mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have hone : g' i₀ = 1 := inv_mul_cancel₀ hne
  have hfixc : ∀ σ : L ≃ₐ[k] L, ∀ i ∈ s, σ (g' i) = g' i := by
    intro σ
    have h1 : ∑ i ∈ s, σ (g' i) • v i = 0 := by
      have := congrArg (ρ σ) hg'
      simpa [map_sum, hρ, hfix] using this
    have h2 : ∑ i ∈ s.erase i₀, (σ (g' i) - g' i) • v i = 0 := by
      rw [Finset.sum_erase _ (by rw [hone, map_one, sub_self, zero_smul])]
      simp only [sub_smul, Finset.sum_sub_distrib, h1, hg', sub_zero]
    have h3 := ih (s.erase i₀) (Finset.erase_ssubset hi₀) _ h2
    intro i hi
    by_cases hii : i = i₀
    · rw [hii, hone, map_one]
    · exact sub_eq_zero.1 (h3 i (Finset.mem_erase.2 ⟨hii, hi⟩))
  have hk : ∀ i, ∃ c : k, algebraMap k L c = if i ∈ s then g' i else 0 := fun i => by
    split_ifs with hi
    · exact (IsGalois.mem_range_algebraMap_iff_fixed (F := k) _).2 fun σ => hfixc σ i hi
    · exact ⟨0, map_zero _⟩
  choose c hc using hk
  have hsum : ∑ i ∈ s, c i • v i = 0 := by
    rw [← hg']
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← algebraMap_smul L, hc]
    simp only [hi, ite_true]
  have hc0 := linearIndependent_iff'.1 hv s c hsum i₀ hi₀
  have := hc i₀
  simp only [hi₀, ite_true, hone, hc0, map_zero] at this
  exact zero_ne_one this

/-- **Galois descent for vector spaces**: `L ⊗[k] V^ρ ≅ V` by `c ⊗ v ↦ c • v`. -/
theorem bijective_liftBaseChange_fixedPoints (hone : ∀ v, ρ 1 v = v)
    (hmul : ∀ σ τ v, ρ (σ * τ) v = ρ σ (ρ τ v)) :
    Function.Bijective ((fixedPoints ρ hρ).subtype.liftBaseChange L) := by
  classical
  set b := Basis.ofVectorSpace k (fixedPoints ρ hρ)
  constructor
  · refine LinearMap.injective_of_linearIndependent (v := b.baseChange L)
      (b.baseChange L).span_eq ?_
    have : ((fixedPoints ρ hρ).subtype.liftBaseChange L) ∘ (b.baseChange L) =
        fun i => (b i : V) := funext fun i => by
      simp [Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
    rw [this]
    have hk : LinearIndependent k (fun i => (b i : V)) :=
      b.linearIndependent.map' (fixedPoints ρ hρ).subtype (Submodule.ker_subtype _)
    have hfix : ∀ σ i, ρ σ (b i : V) = b i := fun σ i => (b i).2 σ
    exact linearIndependent_of_fixed ρ hρ _ hfix hk
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← span_fixedPoints ρ hρ hone hmul,
      Submodule.span_le]
    intro v hv
    exact ⟨(1 : L) ⊗ₜ ⟨v, hv⟩, by simp [LinearMap.liftBaseChange_tmul]⟩

end Speiser

end GaloisDescent
