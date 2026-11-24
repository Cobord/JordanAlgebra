module

public import JordanDiagram.Algebra.OrthogonalFlag

/-!
# Orthogonal flags: isomorphisms and the Lie algebra

Let `V = ⨁ᵢ Uᵢ` and `V' = ⨁ᵢ U'ᵢ` be internal direct sums of mutually orthogonal pieces, indexed
by the same finite linear order, with the forms nondegenerate on every piece, and let
`W_j = ⨆_{i ≤ j} Uᵢ`, `W'_j = ⨆_{i ≤ j} U'ᵢ` be the flags.

* `nonempty_flagIsometry_iff`: there is an isometry `V ≃ V'` carrying every `W_j` onto `W'_j`
  exactly when every piece `Uᵢ` is isometric to `U'ᵢ`. Such an isometry restricts to isometries
  of the pieces (`flagIsometry_mem_piece`), and isometries of the pieces glue.
* `skewFlagEquivPi`: the Lie algebra analogue of `stabFlagEquivPi`. The `B`-skew endomorphisms of
  `V` preserving every `W_j` correspond to the families of `B`-skew endomorphisms of the pieces,
  `o(V, B)_W ≅ ⊕ᵢ o(Uᵢ, B)`, by restriction. It is linear, and the bracket is the commutator on both
  sides, so restriction also preserves brackets.
-/

@[expose] public section

noncomputable section

namespace SpinFactor

variable {R V V' : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup V']
  [Module R V']
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable {B : LinearMap.BilinForm R V} {B' : LinearMap.BilinForm R V'}
  {U : ι → Submodule R V} {U' : ι → Submodule R V'}
  (hU : DirectSum.IsInternal U) (hU' : DirectSum.IsInternal U')

section Maps

omit [Fintype ι] [DecidableEq ι]

/-- A linear map carrying every piece into the corresponding piece preserves the flags. -/
theorem map_mem_flagMember (f : V →ₗ[R] V') (hf : ∀ i, ∀ u ∈ U i, f u ∈ U' i) {j : ι} {v : V}
    (hv : v ∈ flagMember U j) : f v ∈ flagMember U' j := by
  induction hv using Submodule.iSup_induction' with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem i u hu => exact mem_flagMember_of_mem i.2 (hf i u hu)

/-- A linear map preserving the flags preserves the parts below each index. -/
theorem map_mem_flagBelow (f : V →ₗ[R] V')
    (hf : ∀ j, ∀ v ∈ flagMember U j, f v ∈ flagMember U' j) {j : ι} {v : V}
    (hv : v ∈ flagBelow U j) : f v ∈ flagBelow U' j := by
  rw [flagBelow_eq] at hv ⊢
  induction hv using Submodule.iSup_induction' with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem i u hu => exact Submodule.mem_iSup_of_mem i (hf i.1 u hu)

end Maps

section Iso

variable (B B' U U') in
/-- The isometries `(V, B) ≃ (V', B')` carrying every flag member `W_j` onto `W'_j`. -/
def FlagIsometry : Type _ :=
  {g : Isometry B B' // ∀ j v, g.1 v ∈ flagMember U' j ↔ v ∈ flagMember U j}

omit [Fintype ι] [DecidableEq ι] in
/-- The inverse of a flag isometry. -/
def FlagIsometry.symm (g : FlagIsometry B B' U U') : FlagIsometry B' B U' U :=
  ⟨⟨g.1.1.symm, fun v w => by
    rw [← g.1.2 (g.1.1.symm v) (g.1.1.symm w), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]⟩, fun j v => by
    rw [← g.2 j, LinearEquiv.apply_symm_apply]⟩

omit [Fintype ι] [DecidableEq ι] in
theorem FlagIsometry.mem_flagMember (g : FlagIsometry B B' U U') {j : ι} {v : V}
    (hv : v ∈ flagMember U j) : g.1.1 v ∈ flagMember U' j :=
  (g.2 j v).2 hv

include hU' in
/-- A flag isometry carries each piece `Uⱼ` into `U'ⱼ`. -/
theorem flagIsometry_mem_piece (hO : PairwiseOrthogonal B U) (hO' : PairwiseOrthogonal B' U')
    (hN' : ∀ i, NondegenerateOn B' (U' i)) (g : FlagIsometry B B' U U') {j : ι} {u : V}
    (hu : u ∈ U j) : g.1.1 u ∈ U' j := by
  refine mem_piece_of_orthogonal hU' hO' hN' (g.mem_flagMember (mem_flagMember_of_mem le_rfl hu))
    fun y hy => ?_
  have hz : g.1.1.symm y ∈ flagBelow U j :=
    map_mem_flagBelow g.1.1.symm.toLinearMap (fun _ _ hv => g.symm.mem_flagMember hv) hy
  rw [← g.1.1.apply_symm_apply y, g.1.2]
  exact apply_eq_zero_of_mem_flagBelow hO hu hz

include hU hU' in
/-- A flag isometry restricts to an isometry of the pieces `Uᵢ ≃ U'ᵢ`. -/
def FlagIsometry.restrictPiece (hO : PairwiseOrthogonal B U) (hO' : PairwiseOrthogonal B' U')
    (hN : ∀ i, NondegenerateOn B (U i)) (hN' : ∀ i, NondegenerateOn B' (U' i))
    (g : FlagIsometry B B' U U') (i : ι) : Isometry (B.restrict (U i)) (B'.restrict (U' i)) :=
  ⟨g.1.1.ofSubmodules (U i) (U' i) (by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact flagIsometry_mem_piece hU' hO hO' hN' g hv
    · intro hx
      refine ⟨g.1.1.symm x, flagIsometry_mem_piece hU hO' hO hN g.symm hx,
        LinearEquiv.apply_symm_apply _ _⟩), fun x y => g.1.2 x y⟩

include hU hU' in
/-- **Isomorphism of orthogonal flags**: two orthogonal flags with nondegenerate pieces are
isometric (by an isometry carrying `W_j` onto `W'_j` for every `j`) exactly when their pieces are
pairwise isometric. -/
theorem nonempty_flagIsometry_iff (hO : PairwiseOrthogonal B U) (hO' : PairwiseOrthogonal B' U')
    (hN : ∀ i, NondegenerateOn B (U i)) (hN' : ∀ i, NondegenerateOn B' (U' i)) :
    Nonempty (FlagIsometry B B' U U') ↔
      ∀ i, Nonempty (Isometry (B.restrict (U i)) (B'.restrict (U' i))) := by
  constructor
  · rintro ⟨g⟩ i
    exact ⟨g.restrictPiece hU hU' hO hO' hN hN' i⟩
  · intro h
    let gs := fun i => (h i).some
    set G := glueEquivPieces hU hU' fun i => (gs i).1
    have hG := glueEquivPieces_mem_iff hU hU' fun i => (gs i).1
    refine ⟨⟨⟨G, glueEquivPieces_isometry hU hU' hO hO' _ fun i => (gs i).2⟩, fun j v => ?_⟩⟩
    refine ⟨fun hv => ?_, map_mem_flagMember G.toLinearMap (fun i u hu => (hG i u).2 hu)⟩
    have := map_mem_flagMember G.symm.toLinearMap (fun i u hu => (hG i _).1 (by
      change G (G.symm u) ∈ U' i
      rwa [LinearEquiv.apply_symm_apply])) hv
    rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this

end Iso

section Lie

variable (B) in
/-- The `B`-skew endomorphisms `o(V, B)`, as a submodule of `End V`. -/
def skewSub : Submodule R (V →ₗ[R] V) where
  carrier := {X | IsSkew B X}
  add_mem' {_ _} hX hY v w := by
    simp only [LinearMap.add_apply, map_add, LinearMap.add_apply]
    rw [add_add_add_comm, hX v w, hY v w, add_zero]
  zero_mem' v w := by simp
  smul_mem' r _ hX v w := by
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_add, hX v w, mul_zero]

variable (B U) in
/-- The `B`-skew endomorphisms of `V` preserving every flag member `W_j`. -/
def skewFlagSub : Submodule R (V →ₗ[R] V) where
  carrier := {X | IsSkew B X ∧ ∀ j, ∀ v ∈ flagMember U j, X v ∈ flagMember U j}
  add_mem' {_ _} hX hY := ⟨(skewSub B).add_mem hX.1 hY.1, fun j v hv =>
    add_mem (hX.2 j v hv) (hY.2 j v hv)⟩
  zero_mem' := ⟨(skewSub B).zero_mem, fun _ _ _ => zero_mem _⟩
  smul_mem' r _ hX := ⟨(skewSub B).smul_mem r hX.1, fun j v hv =>
    Submodule.smul_mem _ r (hX.2 j v hv)⟩

include hU in
/-- A skew endomorphism preserving the flag maps every piece into itself. -/
theorem skewFlag_mem_piece (hO : PairwiseOrthogonal B U) (hN : ∀ i, NondegenerateOn B (U i))
    {X : V →ₗ[R] V} (hX : X ∈ skewFlagSub B U) {j : ι} {u : V} (hu : u ∈ U j) : X u ∈ U j := by
  refine mem_piece_of_orthogonal hU hO hN (hX.2 j u (mem_flagMember_of_mem le_rfl hu))
    fun y hy => ?_
  have hz : X y ∈ flagBelow U j := map_mem_flagBelow X hX.2 hy
  rw [eq_neg_of_add_eq_zero_left (hX.1 u y), apply_eq_zero_of_mem_flagBelow hO hu hz, neg_zero]

omit [LinearOrder ι] in
include hU in
/-- Glued skew endomorphisms of mutually orthogonal pieces are skew. -/
theorem glueLin_isSkew (hO : PairwiseOrthogonal B U) (Ys : ∀ i, skewSub (B.restrict (U i)))
    (v w : V) :
    B (glueLin hU (fun i => (Ys i).1) v) w + B v (glueLin hU (fun i => (Ys i).1) w) = 0 := by
  induction mem_iSup_of_isInternal hU v using Submodule.iSup_induction' with
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [add_add_add_comm, hx, hy, add_zero]
  | mem i x hx =>
    induction mem_iSup_of_isInternal hU w using Submodule.iSup_induction' with
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add]
      rw [add_add_add_comm, hy, hz, add_zero]
    | mem j y hy =>
      rw [glueLin_of_mem hU _ hx, glueLin_of_mem hU _ hy]
      by_cases hij : i = j
      · subst hij
        exact (Ys i).2 ⟨x, hx⟩ ⟨y, hy⟩
      · rw [hO i j hij _ ((Ys i).1 ⟨x, hx⟩).2 y hy, hO i j hij x hx _ ((Ys j).1 ⟨y, hy⟩).2,
          add_zero]

/-- **Orthogonal flags, Lie algebra**: for an internal direct sum of mutually orthogonal pieces
on which `B` is nondegenerate, the `B`-skew endomorphisms preserving the flag
`W_j = ⨆_{i ≤ j} Uᵢ` are the families of `B`-skew endomorphisms of the pieces, by restriction. -/
def skewFlagEquivPi (hO : PairwiseOrthogonal B U) (hN : ∀ i, NondegenerateOn B (U i)) :
    skewFlagSub B U ≃ₗ[R] ∀ i, skewSub (B.restrict (U i)) where
  toFun X i := ⟨X.1.restrict fun _ hu => skewFlag_mem_piece hU hO hN X.2 hu,
    fun x y => X.2.1 x y⟩
  map_add' _ _ := funext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := funext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  invFun Ys := ⟨glueLin hU fun i => (Ys i).1, glueLin_isSkew hU hO Ys, fun _ _ hv =>
    map_mem_flagMember _ (fun i u hu => by rw [glueLin_of_mem hU _ hu]; exact ((Ys i).1 _).2) hv⟩
  left_inv X := Subtype.ext (linearMap_ext_of_pieces hU fun i u hu => glueLin_of_mem hU _ hu)
  right_inv Ys := funext fun i => Subtype.ext (LinearMap.ext fun u =>
    Subtype.ext (glueLin_of_mem hU _ u.2))

/-- The equivalence `skewFlagEquivPi` is restriction to the pieces. -/
theorem skewFlagEquivPi_apply (hO : PairwiseOrthogonal B U) (hN : ∀ i, NondegenerateOn B (U i))
    (X : skewFlagSub B U) (i : ι) (u : U i) :
    ((skewFlagEquivPi hU hO hN X i : U i →ₗ[R] U i) u : V) = X.1 u := rfl

end Lie

end SpinFactor

end
