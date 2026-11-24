module

public import JordanDiagram.Algebra.Orthogonal
public import Mathlib.Algebra.DirectSum.Module

/-!
# Orthogonal decompositions and flags

Let `B` be a bilinear form on `V`, and `V = ⨁ᵢ Uᵢ` an internal direct sum (`DirectSum.IsInternal`)
of mutually `B`-orthogonal submodules (`PairwiseOrthogonal`), over a finite index type.

* `stabPiecesEquivPi`: the isometries of `(V, B)` preserving every `Uᵢ` form the product
  `∏ᵢ O(Uᵢ, B)`, by restriction to the pieces. Gluing isometries of the pieces back together
  inverts it. No nondegeneracy is needed.
* `stabFlagEquivPi`: for a linearly ordered index type, the flag `W_j = ⨆_{i ≤ j} Uᵢ`
  (`flagMember`) has the same stabilizer when `B` is nondegenerate on every piece: an isometry
  preserving every `W_j` preserves every `U_j = W_j ∩ (⨆_{i < j} Uᵢ)^⊥`. So the stabilizer of the
  flag in `O(V, B)` is `∏ⱼ O(U_j, B)`.

A flag whose members carry nonsingular forms has such an orthogonal decomposition into pieces
(by `isCompl_orthogonal`, applied to consecutive members); the pieces are the input here.
-/

@[expose] public section

noncomputable section

namespace SpinFactor

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The submodules `U i` are mutually `B`-orthogonal. -/
def PairwiseOrthogonal (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) : Prop :=
  ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0

/-- `B` is nondegenerate on `W`: only `0` is `B`-orthogonal to all of `W` inside `W`. -/
def NondegenerateOn (B : LinearMap.BilinForm R V) (W : Submodule R V) : Prop :=
  ∀ u ∈ W, (∀ w ∈ W, B u w = 0) → u = 0

variable {U : ι → Submodule R V} (hU : DirectSum.IsInternal U)

section Projections

/-- The projection `V → U k` of an internal direct sum. -/
def proj (k : ι) : V →ₗ[R] U k :=
  DirectSum.component R ι (fun i => U i) k ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap U) hU).symm.toLinearMap

omit [Fintype ι] in
theorem proj_apply (k : ι) (v : V) :
    proj hU k v = (LinearEquiv.ofBijective (DirectSum.coeLinearMap U) hU).symm v k := rfl

omit [Fintype ι] in
theorem proj_of_mem {k : ι} {u : V} (hu : u ∈ U k) : proj hU k u = ⟨u, hu⟩ := by
  rw [proj_apply]
  exact hU.ofBijective_coeLinearMap_of_mem hu

omit [Fintype ι] in
theorem proj_of_mem_ne {i k : ι} (hik : i ≠ k) {u : V} (hu : u ∈ U i) : proj hU k u = 0 := by
  rw [proj_apply]
  exact hU.ofBijective_coeLinearMap_of_mem_ne hik hu

/-- Every vector is the sum of its components. -/
theorem sum_proj (v : V) : ∑ k, (proj hU k v : V) = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap U) hU
  calc ∑ k, (proj hU k v : V)
      = DirectSum.coeLinearMap U (∑ k, DirectSum.of (fun i => U i) k (e.symm v k)) := by
        rw [map_sum]
        simp only [DirectSum.coeLinearMap_of, proj_apply]
        rfl
    _ = e (e.symm v) := by rw [DirectSum.sum_univ_of]; rfl
    _ = v := e.apply_symm_apply v

omit [Fintype ι] in
include hU in
theorem mem_iSup_of_isInternal (v : V) : v ∈ ⨆ i, U i :=
  hU.submodule_iSup_eq_top ▸ Submodule.mem_top

omit [Fintype ι] in
include hU in
/-- Linear maps out of `V` agreeing on every piece are equal. -/
theorem linearMap_ext_of_pieces {N : Type*} [AddCommGroup N] [Module R N] {f g : V →ₗ[R] N}
    (h : ∀ i, ∀ u ∈ U i, f u = g u) : f = g := by
  ext v
  induction mem_iSup_of_isInternal hU v using Submodule.iSup_induction' with
  | mem i u hu => exact h i u hu
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

end Projections

section Glue

variable {B : LinearMap.BilinForm R V}

/-- Gluing linear maps of the pieces: `v ↦ ∑ₖ gₖ (proj_k v)`. -/
def glueLin (gs : ∀ i, U i →ₗ[R] U i) : V →ₗ[R] V :=
  ∑ k, (U k).subtype ∘ₗ gs k ∘ₗ proj hU k

theorem glueLin_of_mem (gs : ∀ i, U i →ₗ[R] U i) {i : ι} {u : V} (hu : u ∈ U i) :
    glueLin hU gs u = gs i ⟨u, hu⟩ := by
  simp only [glueLin, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [Finset.sum_eq_single i]
  · rw [proj_of_mem hU hu]
  · intro k _ hki
    rw [proj_of_mem_ne hU (Ne.symm hki) hu, map_zero, Submodule.coe_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem glueLin_comp (gs hs : ∀ i, U i →ₗ[R] U i) :
    glueLin hU gs ∘ₗ glueLin hU hs = glueLin hU (fun i => gs i ∘ₗ hs i) :=
  linearMap_ext_of_pieces hU fun i u hu => by
    rw [LinearMap.comp_apply, glueLin_of_mem hU hs hu, glueLin_of_mem hU gs (hs i ⟨u, hu⟩).2,
      glueLin_of_mem hU _ hu]
    rfl

theorem glueLin_id : glueLin hU (fun i => LinearMap.id (R := R) (M := U i)) = LinearMap.id :=
  linearMap_ext_of_pieces hU fun i u hu => by rw [glueLin_of_mem hU _ hu]; rfl

/-- Gluing linear automorphisms of the pieces. -/
def glueEquivPieces (gs : ∀ i, U i ≃ₗ[R] U i) : V ≃ₗ[R] V :=
  LinearEquiv.ofLinearMap (glueLin hU fun i => (gs i).toLinearMap)
    (glueLin hU fun i => (gs i).symm.toLinearMap)
    (by rw [glueLin_comp]; simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap]; exact glueLin_id hU)
    (by rw [glueLin_comp]; simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap]; exact glueLin_id hU)

theorem glueEquivPieces_of_mem (gs : ∀ i, U i ≃ₗ[R] U i) {i : ι} {u : V} (hu : u ∈ U i) :
    glueEquivPieces hU gs u = gs i ⟨u, hu⟩ :=
  glueLin_of_mem hU _ hu

theorem glueEquivPieces_symm_of_mem (gs : ∀ i, U i ≃ₗ[R] U i) {i : ι} {u : V} (hu : u ∈ U i) :
    (glueEquivPieces hU gs).symm u = (gs i).symm ⟨u, hu⟩ :=
  glueLin_of_mem hU _ hu

theorem glueEquivPieces_mem_iff (gs : ∀ i, U i ≃ₗ[R] U i) (i : ι) (v : V) :
    glueEquivPieces hU gs v ∈ U i ↔ v ∈ U i := by
  constructor
  · intro h
    have := glueEquivPieces_symm_of_mem hU gs h
    rw [LinearEquiv.symm_apply_apply] at this
    rw [this]
    exact ((gs i).symm _).2
  · intro h
    rw [glueEquivPieces_of_mem hU gs h]
    exact (gs i ⟨v, h⟩).2

/-- Glued isometries of mutually orthogonal pieces form an isometry. -/
theorem glueEquivPieces_isometry (hO : PairwiseOrthogonal B U)
    (gs : ∀ i, orthogonalGroup (B.restrict (U i))) (v w : V) :
    B (glueEquivPieces hU (fun i => (gs i).1) v) (glueEquivPieces hU (fun i => (gs i).1) w) =
      B v w := by
  induction mem_iSup_of_isInternal hU v using Submodule.iSup_induction' with
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | mem i x hx =>
    induction mem_iSup_of_isInternal hU w using Submodule.iSup_induction' with
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | mem j y hy =>
      rw [glueEquivPieces_of_mem hU _ hx, glueEquivPieces_of_mem hU _ hy]
      by_cases hij : i = j
      · subst hij
        exact (gs i).2 ⟨x, hx⟩ ⟨y, hy⟩
      · rw [hO i j hij _ ((gs i).1 ⟨x, hx⟩).2 _ ((gs j).1 ⟨y, hy⟩).2, hO i j hij x hx y hy]

end Glue

section Stabilizers

omit [Fintype ι] [DecidableEq ι] in
/-- An isometry preserving a family of submodules (in the `↔` sense) has inverse preserving it. -/
theorem inv_mem_iff_of_mem_iff {B : LinearMap.BilinForm R V} {P : Submodule R V}
    {g : orthogonalGroup B} (hg : ∀ v, (g : V ≃ₗ[R] V) v ∈ P ↔ v ∈ P) (v : V) :
    ((g⁻¹ : orthogonalGroup B) : V ≃ₗ[R] V) v ∈ P ↔ v ∈ P := by
  change (g : V ≃ₗ[R] V).symm v ∈ P ↔ _
  rw [← hg, LinearEquiv.apply_symm_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem mem_iff_of_forall_mem {B : LinearMap.BilinForm R V} {P : Submodule R V}
    {g : orthogonalGroup B} (h1 : ∀ v ∈ P, (g : V ≃ₗ[R] V) v ∈ P)
    (h2 : ∀ v ∈ P, ((g⁻¹ : orthogonalGroup B) : V ≃ₗ[R] V) v ∈ P) (v : V) :
    (g : V ≃ₗ[R] V) v ∈ P ↔ v ∈ P := by
  refine ⟨fun h => ?_, h1 v⟩
  have := h2 _ h
  rwa [show ((g⁻¹ : orthogonalGroup B) : V ≃ₗ[R] V) ((g : V ≃ₗ[R] V) v) = v from
    (g.1 : V ≃ₗ[R] V).symm_apply_apply v] at this

omit [Fintype ι] [DecidableEq ι] in
/-- The isometries preserving every member of a family of submodules. -/
def stabFamily (B : LinearMap.BilinForm R V) {κ : Type*} (P : κ → Submodule R V) :
    Subgroup (orthogonalGroup B) where
  carrier := {g | ∀ k v, (g : V ≃ₗ[R] V) v ∈ P k ↔ v ∈ P k}
  one_mem' _ _ := Iff.rfl
  mul_mem' {g h} hg hh k v := by
    change (g : V ≃ₗ[R] V) ((h : V ≃ₗ[R] V) v) ∈ P k ↔ _
    rw [hg, hh]
  inv_mem' {g} hg k v := inv_mem_iff_of_mem_iff (hg k) v

/-- The isometries preserving every piece `U i`. -/
abbrev stabPieces (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) :
    Subgroup (orthogonalGroup B) :=
  stabFamily B U

/-- Restriction to the pieces, as a group homomorphism. -/
def stabPiecesToPi (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) :
    stabPieces B U →* ∀ i, orthogonalGroup (B.restrict (U i)) where
  toFun g i := restrictOrth g.1 (U i) (g.2 i)
  map_one' := rfl
  map_mul' _ _ := rfl

variable {B : LinearMap.BilinForm R V}

omit [Fintype ι] in
include hU in
theorem stabPiecesToPi_injective : Function.Injective (stabPiecesToPi B U) := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine linearMap_ext_of_pieces hU fun i u hu => ?_
  exact congrArg (fun k : ∀ i, orthogonalGroup (B.restrict (U i)) => ((k i).1 ⟨u, hu⟩ : V)) hgh

/-- **Orthogonal decomposition**: the isometries preserving every piece of an internal direct
sum of mutually orthogonal submodules form `∏ᵢ O(Uᵢ, B)`, by restriction to the pieces. -/
def stabPiecesEquivPi (hO : PairwiseOrthogonal B U) :
    stabPieces B U ≃* ∀ i, orthogonalGroup (B.restrict (U i)) :=
  MulEquiv.ofBijective (stabPiecesToPi B U) ⟨stabPiecesToPi_injective hU, fun gs =>
    ⟨⟨⟨glueEquivPieces hU (fun i => (gs i).1), glueEquivPieces_isometry hU hO gs⟩,
      glueEquivPieces_mem_iff hU _⟩, by
      funext i
      apply Subtype.ext
      apply LinearEquiv.ext
      intro u
      exact Subtype.ext (glueEquivPieces_of_mem hU _ u.2)⟩⟩

end Stabilizers

section Flag

variable [LinearOrder ι]

variable (U) in
/-- The flag member `W_j = ⨆_{i ≤ j} Uᵢ`. -/
def flagMember (j : ι) : Submodule R V := ⨆ i : {i : ι // i ≤ j}, U i

variable (U) in
/-- The part strictly below `j`: `⨆_{i < j} Uᵢ`. -/
def flagBelow (j : ι) : Submodule R V := ⨆ i : {i : ι // i < j}, U i

/-- The isometries preserving every flag member `W_j`. -/
abbrev stabFlag (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) :
    Subgroup (orthogonalGroup B) :=
  stabFamily B (flagMember U)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_flagMember_of_mem {i j : ι} (hij : i ≤ j) {u : V} (hu : u ∈ U i) :
    u ∈ flagMember U j :=
  Submodule.mem_iSup_of_mem (⟨i, hij⟩ : {i : ι // i ≤ j}) hu

omit [Fintype ι] [DecidableEq ι] in
theorem mem_flagBelow_of_mem {i j : ι} (hij : i < j) {u : V} (hu : u ∈ U i) :
    u ∈ flagBelow U j :=
  Submodule.mem_iSup_of_mem (⟨i, hij⟩ : {i : ι // i < j}) hu

omit [Fintype ι] [DecidableEq ι] in
/-- The part below `j` is the supremum of the flag members below `j`. -/
theorem flagBelow_eq (j : ι) :
    flagBelow U j = ⨆ i : {i : ι // i < j}, flagMember U i.1 := by
  apply le_antisymm
  · exact iSup_le fun i => le_trans
      (le_iSup (fun k : {k : ι // k ≤ i.1} => U k.1) ⟨i.1, le_rfl⟩)
      (le_iSup (fun i : {i : ι // i < j} => flagMember U i.1) i)
  · exact iSup_le fun i => iSup_le fun k =>
      le_iSup_of_le (⟨k.1, lt_of_le_of_lt k.2 i.2⟩ : {k : ι // k < j}) le_rfl

omit [Fintype ι] [LinearOrder ι] in
/-- A vector in `⨆_{i ∈ S} Uᵢ` has no component outside `S`. -/
theorem proj_eq_zero_of_mem_iSup (S : ι → Prop) {x : V} (hx : x ∈ ⨆ i : {i : ι // S i}, U i)
    {k : ι} (hk : ¬ S k) : proj hU k x = 0 := by
  induction hx using Submodule.iSup_induction' with
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mem i u hu => exact proj_of_mem_ne hU (fun h => hk (by rw [← h]; exact i.2)) hu

variable {B : LinearMap.BilinForm R V}

omit [LinearOrder ι] in
/-- Pairing against a piece only sees the component in that piece. -/
theorem apply_eq_proj (hO : PairwiseOrthogonal B U) (v : V) {k : ι} {y : V} (hy : y ∈ U k) :
    B v y = B (proj hU k v) y := by
  conv_lhs => rw [← sum_proj hU v]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single k]
  · intro i _ hik
    exact hO i k hik _ (proj hU i v).2 y hy
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [Fintype ι] [DecidableEq ι] in
/-- A vector of a piece `U j` is orthogonal to everything below `j`. -/
theorem apply_eq_zero_of_mem_flagBelow (hO : PairwiseOrthogonal B U) {j : ι} {u y : V}
    (hu : u ∈ U j) (hy : y ∈ flagBelow U j) : B u y = 0 := by
  induction hy using Submodule.iSup_induction' with
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp, hq, add_zero]
  | mem i w hw => exact hO j i (Ne.symm (ne_of_lt i.2)) u hu w hw

include hU in
/-- An orthogonal sum of nondegenerate pieces is nondegenerate: a vector of `⨆_{i<j} Uᵢ`
orthogonal to all of it is zero. -/
theorem eq_zero_of_mem_flagBelow (hO : PairwiseOrthogonal B U)
    (hN : ∀ i, NondegenerateOn B (U i)) {j : ι} {a : V} (ha : a ∈ flagBelow U j)
    (horth : ∀ y ∈ flagBelow U j, B a y = 0) : a = 0 := by
  rw [← sum_proj hU a]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < j
  · have := hN k (proj hU k a) (proj hU k a).2 fun y hy => by
      rw [← apply_eq_proj hU hO a hy]
      exact horth y (mem_flagBelow_of_mem hk hy)
    exact this
  · rw [proj_eq_zero_of_mem_iSup hU (· < j) ha hk, Submodule.coe_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem stabPieces_le_stabFlag : stabPieces B U ≤ stabFlag B U := by
  intro g hg j
  have key : ∀ (h : orthogonalGroup B), (∀ i v, (h : V ≃ₗ[R] V) v ∈ U i ↔ v ∈ U i) →
      ∀ v ∈ flagMember U j, (h : V ≃ₗ[R] V) v ∈ flagMember U j := by
    intro h hh v hv
    induction hv using Submodule.iSup_induction' with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mem i u hu => exact mem_flagMember_of_mem i.2 ((hh i u).2 hu)
  exact mem_iff_of_forall_mem (key g hg) (key g⁻¹ ((stabPieces B U).inv_mem hg))

omit [Fintype ι] [DecidableEq ι] in
/-- An isometry preserving the flag preserves the part below each `j`. -/
theorem stabFlag_mem_flagBelow {g : orthogonalGroup B} (hg : g ∈ stabFlag B U) (j : ι) {v : V}
    (hv : v ∈ flagBelow U j) : (g : V ≃ₗ[R] V) v ∈ flagBelow U j := by
  rw [flagBelow_eq] at hv ⊢
  induction hv using Submodule.iSup_induction' with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem i u hu => exact Submodule.mem_iSup_of_mem i ((hg i.1 u).2 hu)

include hU in
/-- An isometry preserving the flag maps `U_j` into `U_j`: `g u` lies in `W_j`, and its part
below `j` is orthogonal to all of `⨆_{i<j} Uᵢ`, hence zero. -/
theorem stabFlag_mem_piece (hO : PairwiseOrthogonal B U) (hN : ∀ i, NondegenerateOn B (U i))
    {g : orthogonalGroup B} (hg : g ∈ stabFlag B U) (j : ι) {u : V} (hu : u ∈ U j) :
    (g : V ≃ₗ[R] V) u ∈ U j := by
  set x := (g : V ≃ₗ[R] V) u with hx_def
  have hx : x ∈ flagMember U j := (hg j u).2 (mem_flagMember_of_mem le_rfl hu)
  set a := x - (proj hU j x : V)
  have ha : a ∈ flagBelow U j := by
    have hrest : ∑ k ∈ Finset.univ.filter (fun k => ¬ k < j), (proj hU k x : V) =
        (proj hU j x : V) := by
      rw [Finset.sum_eq_single j]
      · intro k hk hkj
        have hk' : ¬ k < j := (Finset.mem_filter.1 hk).2
        have hjk : ¬ k ≤ j := fun h => hk' (lt_of_le_of_ne h hkj)
        rw [proj_eq_zero_of_mem_iSup hU (· ≤ j) hx hjk, Submodule.coe_zero]
      · intro h
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, lt_irrefl j⟩) h
    have hsum : a = ∑ k ∈ Finset.univ.filter (· < j), (proj hU k x : V) := by
      have h := sum_proj hU x
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < j), hrest] at h
      change x - _ = _
      rw [eq_comm, eq_sub_iff_add_eq]
      exact h
    rw [hsum]
    exact Submodule.sum_mem _ fun k hk =>
      mem_flagBelow_of_mem (Finset.mem_filter.1 hk).2 (proj hU k x).2
  have horth : ∀ y ∈ flagBelow U j, B a y = 0 := by
    intro y hy
    have hz : ((g⁻¹ : orthogonalGroup B) : V ≃ₗ[R] V) y ∈ flagBelow U j :=
      stabFlag_mem_flagBelow ((stabFlag B U).inv_mem hg) j hy
    have hyz : y = (g : V ≃ₗ[R] V) (((g⁻¹ : orthogonalGroup B) : V ≃ₗ[R] V) y) :=
      ((g.1 : V ≃ₗ[R] V).apply_symm_apply y).symm
    have h1 : B x y = 0 := by
      rw [hyz, hx_def, g.2]
      exact apply_eq_zero_of_mem_flagBelow hO hu hz
    rw [map_sub, LinearMap.sub_apply, h1,
      apply_eq_zero_of_mem_flagBelow hO (proj hU j x).2 hy, sub_zero]
  have := eq_zero_of_mem_flagBelow hU hO hN ha horth
  rw [sub_eq_zero] at this
  rw [this]
  exact (proj hU j x).2

include hU in
theorem stabFlag_le_stabPieces (hO : PairwiseOrthogonal B U)
    (hN : ∀ i, NondegenerateOn B (U i)) : stabFlag B U ≤ stabPieces B U := fun _ hg j =>
  mem_iff_of_forall_mem (fun _ => stabFlag_mem_piece hU hO hN hg j)
    (fun _ => stabFlag_mem_piece hU hO hN ((stabFlag B U).inv_mem hg) j)

/-- **Orthogonal flags**: for an internal direct sum `V = ⨁ U_j` of mutually orthogonal pieces
on which `B` is nondegenerate, the stabilizer in `O(V, B)` of the flag `W_j = ⨆_{i ≤ j} Uᵢ` is
`∏ⱼ O(U_j, B)`, by restriction to the pieces. -/
def stabFlagEquivPi (hO : PairwiseOrthogonal B U) (hN : ∀ i, NondegenerateOn B (U i)) :
    stabFlag B U ≃* ∀ i, orthogonalGroup (B.restrict (U i)) :=
  (MulEquiv.subgroupCongr (le_antisymm (stabFlag_le_stabPieces hU hO hN)
    stabPieces_le_stabFlag)).trans (stabPiecesEquivPi hU hO)

/-- The equivalence `stabFlagEquivPi` is restriction to the pieces. -/
theorem stabFlagEquivPi_apply (hO : PairwiseOrthogonal B U) (hN : ∀ i, NondegenerateOn B (U i))
    (g : stabFlag B U) (i : ι) (u : U i) :
    ((stabFlagEquivPi hU hO hN g i : U i ≃ₗ[R] U i) u : V) = (g : V ≃ₗ[R] V) u := rfl

end Flag

end SpinFactor

end
