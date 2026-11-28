module

public import JordanDiagram.Algebra.DyadicFinite

/-!
# Finiteness for chains of submodules with anisotropic pieces

Let `L₀ ⊆ L₁ ⊆ ⋯ ⊆ Lₙ` be a chain of submodules of `M`, with `Lₙ = M`. The members need not be
direct summands; for example, a member may have finite index in the next. The pieces of the chain
are `L₀` and `L_{j+1} ∩ L_j^⊥` (`chainPiece`).

* `eq_of_forall_chainPiece`: over a domain, for finite free members and a form that is anisotropic
  (`B v v = 0 → v = 0`), two linear maps that agree on every piece agree on every member. The proof
  stays over the base ring. For `v ∈ L_{j+1}`, the adjugate of the Gram matrix `G` of `L_j` gives
  `s ∈ L_j` with `det G • v - s ⊥ L_j`, and `det G ≠ 0` by anisotropy.
* `ZHalf.finite_of_chainPiece`: over `Z[1/2]`, a group of isometries preserving every member is
  finite when every piece has a basis in which the form is positive and anisotropic over `ℚ₂`. The
  sum of the pieces need not have the same property.
-/

@[expose] public section

open Matrix Module

namespace SpinFactor

section Chain

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) {n : ℕ} (L : Fin (n + 1) → Submodule R M)

/-- The vectors `v` with `B w v = 0` for every `w ∈ N`. -/
def rightPerp (N : Submodule R M) : Submodule R M where
  carrier := {v | ∀ w ∈ N, B w v = 0}
  add_mem' hv hv' w hw := by rw [map_add, hv w hw, hv' w hw, add_zero]
  zero_mem' w _ := map_zero _
  smul_mem' c v hv w hw := by rw [map_smul, hv w hw, smul_zero]

/-- The pieces of a chain: `L₀`, and `L_{j+1} ∩ L_j^⊥`. -/
def chainPiece : Fin (n + 1) → Submodule R M :=
  Fin.cases (L 0) fun j => L j.succ ⊓ rightPerp B (L j.castSucc)

theorem mem_chainPiece_zero {v : M} : v ∈ chainPiece B L 0 ↔ v ∈ L 0 := by
  simp [chainPiece]

theorem mem_chainPiece_succ (j : Fin n) {v : M} :
    v ∈ chainPiece B L j.succ ↔ v ∈ L j.succ ∧ ∀ w ∈ L j.castSucc, B w v = 0 := by
  simp only [chainPiece, Fin.cases_succ, Submodule.mem_inf]
  rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {N : Submodule R M}

/-- The Gram matrix of a basis applied to coordinates: `B(b l, ∑ cₖ bₖ) = (G c)_l`. -/
theorem gram_mulVec (b : Basis κ R N) (c : κ → R) (l : κ) :
    B (b l) (b.equivFun.symm c) =
      (LinearMap.BilinForm.toMatrix b (B.restrict N) *ᵥ c) l := by
  simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    smul_eq_mul, mulVec, dotProduct, LinearMap.BilinForm.toMatrix_apply,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Over a domain, the Gram matrix of a basis of a submodule on which the form is anisotropic has
nonzero determinant. -/
theorem det_gram_ne_zero [IsDomain R] (hB : ∀ v, B v v = 0 → v = 0) (b : Basis κ R N) :
    (LinearMap.BilinForm.toMatrix b (B.restrict N)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : B (b.equivFun.symm c) (b.equivFun.symm c) = 0 := by
    have := LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b (B.restrict N)
      (b.equivFun.symm c) (b.equivFun.symm c)
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply, hGc, dotProduct_zero] at this
    exact this
  have h0 : b.equivFun.symm c = 0 := Subtype.ext (hB _ hx)
  exact hc (b.equivFun.symm.injective (by rw [h0, map_zero]))

variable {L}

/-- **Pieces detect the chain**: over a domain, for finite free members and an anisotropic form,
two linear maps agreeing on every piece agree on every member. -/
theorem eq_of_forall_chainPiece [IsDomain R] [IsTorsionFree R M] (hmono : Monotone L)
    (hB : ∀ v, B v v = 0 → v = 0) {κ : Fin (n + 1) → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)] (b : ∀ j, Basis (κ j) R (L j)) (f₁ f₂ : M →ₗ[R] M)
    (hf : ∀ j, ∀ v ∈ chainPiece B L j, f₁ v = f₂ v) : ∀ j, ∀ v ∈ L j, f₁ v = f₂ v := by
  intro j
  induction j using Fin.induction with
  | zero => exact fun v hv => hf 0 v ((mem_chainPiece_zero B L).2 hv)
  | succ j ih =>
    intro v hv
    set G := LinearMap.BilinForm.toMatrix (b j.castSucc) (B.restrict (L j.castSucc))
    have hd : G.det ≠ 0 := det_gram_ne_zero B hB (b j.castSucc)
    set y : κ j.castSucc → R := fun k => B (b j.castSucc k) v
    set s : L j.castSucc := (b j.castSucc).equivFun.symm (G.adjugate *ᵥ y)
    have hs : ∀ l, B (b j.castSucc l) s = G.det * y l := by
      intro l
      rw [gram_mulVec, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
      rfl
    have hmem : G.det • v - (s : M) ∈ chainPiece B L j.succ := by
      rw [mem_chainPiece_succ]
      refine ⟨sub_mem (Submodule.smul_mem _ _ hv)
        (hmono (Fin.castSucc_lt_succ_iff.2 le_rfl).le s.2), fun w hw => ?_⟩
      have key : ((B.flip (G.det • v - (s : M))).comp (L j.castSucc).subtype) = 0 :=
        (b j.castSucc).ext fun l => by
          change B (b j.castSucc l : M) (G.det • v - (s : M)) = 0
          rw [map_sub, map_smul, hs l, smul_eq_mul, sub_self]
      simpa using LinearMap.congr_fun key ⟨w, hw⟩
    have h1 := hf _ _ hmem
    rw [map_sub, map_sub, map_smul, map_smul, ih s s.2] at h1
    exact (smul_right_injective M hd) (sub_left_injective h1)

variable (L)

/-- The stabilizer in `O(M, B)` of every member of the chain. -/
def stabChain : Subgroup (orthogonalGroup B) where
  carrier := {g | ∀ j v, (g : M ≃ₗ[R] M) v ∈ L j ↔ v ∈ L j}
  one_mem' _ _ := Iff.rfl
  mul_mem' {g h} hg hh j v := by
    change (g : M ≃ₗ[R] M) ((h : M ≃ₗ[R] M) v) ∈ _ ↔ _
    rw [hg, hh]
  inv_mem' {g} hg j v := by
    change (g : M ≃ₗ[R] M).symm v ∈ _ ↔ _
    rw [← hg j, LinearEquiv.apply_symm_apply]

theorem mem_stabChain {g : orthogonalGroup B} :
    g ∈ stabChain B L ↔ ∀ j v, (g : M ≃ₗ[R] M) v ∈ L j ↔ v ∈ L j := Iff.rfl

variable {G : Subgroup (orthogonalGroup B)}

/-- An isometry preserving every member of the chain preserves every piece. -/
theorem map_mem_chainPiece {g : orthogonalGroup B}
    (hg : ∀ j v, (g : M ≃ₗ[R] M) v ∈ L j ↔ v ∈ L j) {j : Fin (n + 1)} {v : M}
    (hv : v ∈ chainPiece B L j) : (g : M ≃ₗ[R] M) v ∈ chainPiece B L j := by
  cases j using Fin.cases with
  | zero => exact (mem_chainPiece_zero B L).2 ((hg 0 v).2 ((mem_chainPiece_zero B L).1 hv))
  | succ j =>
    rw [mem_chainPiece_succ] at hv ⊢
    refine ⟨(hg _ v).2 hv.1, fun w hw => ?_⟩
    have hw' : (g : M ≃ₗ[R] M).symm w ∈ L j.castSucc :=
      (hg _ _).1 (by rwa [LinearEquiv.apply_symm_apply])
    have := g.2 ((g : M ≃ₗ[R] M).symm w) v
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this]
    exact hv.2 _ hw'

theorem map_chainPiece {g : orthogonalGroup B} (hg : ∀ j v, (g : M ≃ₗ[R] M) v ∈ L j ↔ v ∈ L j)
    (j : Fin (n + 1)) : (chainPiece B L j).map (g : M ≃ₗ[R] M).toLinearMap = chainPiece B L j := by
  have hg' : ∀ j v, (g⁻¹ : orthogonalGroup B).1 v ∈ L j ↔ v ∈ L j := fun j v => by
    rw [← hg j]
    exact Iff.of_eq (congrArg (· ∈ L j) ((g : M ≃ₗ[R] M).apply_symm_apply v))
  refine le_antisymm ?_ fun v hv => ⟨(g⁻¹ : orthogonalGroup B).1 v,
    map_mem_chainPiece B L hg' hv, (g : M ≃ₗ[R] M).apply_symm_apply v⟩
  rintro _ ⟨v, hv, rfl⟩
  exact map_mem_chainPiece B L hg hv

variable {L} (hG : ∀ g ∈ G, ∀ j v, (g : M ≃ₗ[R] M) v ∈ L j ↔ v ∈ L j)

/-- Restriction of a group of isometries preserving the chain to a piece. The codomain is written
with the submodule's own additive structure, as in `orthRep`. -/
def chainPieceRep (j : Fin (n + 1)) : G →*
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ (chainPiece B L j) (chainPiece B L j)
      (chainPiece B L j).addCommMonoid (chainPiece B L j).addCommMonoid
      (chainPiece B L j).module (chainPiece B L j).module where
  toFun g := (g.1.1 : M ≃ₗ[R] M).ofSubmodules _ _ (map_chainPiece B L (hG g.1 g.2) j)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem chainPieceRep_apply (j : Fin (n + 1)) (g : G) (x : chainPiece B L j) :
    ((chainPieceRep B hG j g x : chainPiece B L j) : M) = (g.1.1 : M ≃ₗ[R] M) x := rfl

theorem chainPieceRep_isometry (j : Fin (n + 1)) (g : G) (x y : chainPiece B L j) :
    B.restrict (chainPiece B L j) (chainPieceRep B hG j g x) (chainPieceRep B hG j g y) =
      B.restrict (chainPiece B L j) x y :=
  g.1.2 x y

/-- **Reduction to the pieces**: over a domain, for finite free members with `Lₙ = M` and an
anisotropic form, a group of isometries preserving every member embeds in the product of its images
on the pieces, so it is finite when each image is. -/
theorem finite_of_finite_chainPieceRep [IsDomain R] [IsTorsionFree R M] (hmono : Monotone L)
    (htop : L (Fin.last n) = ⊤) (hB : ∀ v, B v v = 0 → v = 0) {κ : Fin (n + 1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] (b : ∀ j, Basis (κ j) R (L j))
    (hfin : ∀ j, Finite (chainPieceRep B hG j).range) : Finite G := by
  let φ : G → ∀ j, (chainPieceRep B hG j).range := fun g j => ⟨_, g, rfl⟩
  have hinj : Function.Injective φ := by
    intro g g' hgg'
    have hpiece : ∀ j, ∀ v ∈ chainPiece B L j,
        (g.1.1 : M ≃ₗ[R] M) v = (g'.1.1 : M ≃ₗ[R] M) v := fun j v hv =>
      congrArg (fun e => ((e.1 ⟨v, hv⟩ : chainPiece B L j) : M)) (congrFun hgg' j)
    have hall := eq_of_forall_chainPiece B hmono hB b (g.1.1 : M ≃ₗ[R] M).toLinearMap
      (g'.1.1 : M ≃ₗ[R] M).toLinearMap hpiece
    exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v =>
      hall (Fin.last n) v (htop ▸ Submodule.mem_top)))
  exact Finite.of_injective φ hinj

end Chain

end SpinFactor

namespace ZHalf

open SpinFactor

/-- `Z[1/2]` is a domain, as a localization of `ℤ` away from a nonzero element. -/
instance isDomain : IsDomain ZHalf :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)

variable {M : Type*} [AddCommGroup M] [Module ZHalf M] [IsTorsionFree ZHalf M]
  (B : LinearMap.BilinForm ZHalf M) {n : ℕ} {L : Fin (n + 1) → Submodule ZHalf M}

omit [IsTorsionFree ZHalf M] in
/-- On a piece with a basis in which the form is positive and anisotropic over `ℚ₂`, the image of a
group of isometries preserving the chain is finite. -/
theorem finite_range_chainPieceRep {G : Subgroup (orthogonalGroup B)}
    (hG : ∀ g ∈ G, ∀ j v, (g : M ≃ₗ[ZHalf] M) v ∈ L j ↔ v ∈ L j) {j : Fin (n + 1)}
    {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (bp : Basis κ' ZHalf (chainPiece B L j))
    (hpos : ∀ x : chainPiece B L j, x ≠ 0 → 0 < toRat (B x x))
    (h2 : ∀ v : κ' → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun k k' => ((toRat (B (bp k) (bp k')) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (chainPieceRep B hG j).range :=
  -- the type is left to be inferred from `chainPieceRep`, as for `orthRep`
  finite_of_form (M := chainPiece B L j) bp (ρ := (chainPieceRep B hG j).range.subtype)
    Subtype.val_injective (B.restrict (chainPiece B L j))
    (fun g x y => by
      obtain ⟨g, hg⟩ := g
      obtain ⟨g, rfl⟩ := hg
      exact chainPieceRep_isometry B hG j g x y)
    hpos h2

/-- **Finiteness for chains with anisotropic pieces.** A group of isometries of `M = Lₙ` preserving
every member of a chain of finite free `Z[1/2]`-submodules is finite when the form is positive and
every piece has a basis in which the form is anisotropic over `ℚ₂`. -/
theorem finite_of_chainPiece (hmono : Monotone L) (htop : L (Fin.last n) = ⊤)
    {κ : Fin (n + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (b : ∀ j, Basis (κ j) ZHalf (L j))
    {κ' : Fin (n + 1) → Type*} [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (bp : ∀ j, Basis (κ' j) ZHalf (chainPiece B L j))
    (hpos : ∀ v, v ≠ 0 → 0 < toRat (B v v))
    (h2 : ∀ j (v : κ' j → ℚ_[2]), v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun k k' => ((toRat (B (bp j k) (bp j k')) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0)
    {G : Subgroup (orthogonalGroup B)} (hG : ∀ g ∈ G, ∀ j v, (g : M ≃ₗ[ZHalf] M) v ∈ L j ↔ v ∈ L j) :
    Finite G := by
  have hB : ∀ v, B v v = 0 → v = 0 := fun v h => by
    by_contra hv
    have := hpos v hv
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  exact finite_of_finite_chainPieceRep B hG hmono htop hB b fun j =>
    finite_range_chainPieceRep B hG (bp j)
      (fun x hx => hpos x fun h => hx (Submodule.coe_eq_zero.1 h)) (h2 j)

end ZHalf
