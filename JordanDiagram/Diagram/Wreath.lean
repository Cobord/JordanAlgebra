module

public import JordanDiagram.Diagram.Twisted
public import JordanDiagram.Diagram.SpinFactor
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Twisted automorphisms of spin-factor diagrams, and a wreath product

* `spinTwist`: a shape automorphism `σ` and an isometry `g` of `V` with `g(Wᵢ) = W_{σ i}` give a
  twisted automorphism of the spin-factor diagram, acting by `g ⊕ id` on every node. It is
  multiplicative (`spinTwist_mul`).
* `Disc κ`: a type with the discrete order, so `P⁺ = WithTop (Disc κ)` is `κ` incomparable points
  below a top. Its order automorphisms are the permutations of `κ` (`permShape`,
  `permShape_surjective`).
* `wreathDiagram BU κ`: the spin-factor diagram over `P⁺` of `V = κ → U` with the orthogonal sum
  form `∑ₖ B_U(vₖ, wₖ)`, with the `k`-th copy `Uₖ` of `U` at the node `k` and `V` at the top.
* `wreathEquiv`: for `U` free and `2` invertible, the shape-twisted group of `wreathDiagram BU κ`
  is the wreath product `O(U)^κ ⋊ Perm κ`, compatibly with the shape map
  (`shapeHom_wreathEquiv_symm`).

The proof of bijectivity goes through the exact sequence `1 → G_F → G̃_F → Aut(P⁺)`: every shape
automorphism is a permutation, and `G_F` is `∏ₖ O(Uₖ)`, by terminal determination
(`spinDiagramAutEquiv`).
-/

@[expose] public section

universe u w

open CategoryTheory JordanAlgebra SpinFactor

namespace JordanDiagram

noncomputable section

/-! ### Twisted automorphisms of spin-factor diagrams from isometries -/

section SpinTwist

variable {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
  {B : LinearMap.BilinForm R V} [Fact B.IsSymm]
  {I : Type w} [Preorder I] {W : I →o Submodule R V}

/-- An isometry `g` of `V` carrying each `Wᵢ` onto `W_{σ i}` restricts to isometries
`(Wᵢ, B) ≃ (W_{σ i}, B)`. -/
def pieceIsometry (σ : I ≃o I) (g : orthogonalGroup B)
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i) (i : I) :
    SpinFactor.Isometry (B.restrict (W i)) (B.restrict (W (σ i))) :=
  ⟨(g : V ≃ₗ[R] V).ofSubmodules (W i) (W (σ i)) (by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hg i v).2 hv
    · intro hx
      refine ⟨(g : V ≃ₗ[R] V).symm x, (hg i _).1 ?_, LinearEquiv.apply_symm_apply _ _⟩
      rwa [LinearEquiv.apply_symm_apply]), fun v w => g.2 v w⟩

/-- The twisted automorphism of a spin-factor diagram given by a shape automorphism `σ` and an
isometry `g` carrying each `Wᵢ` onto `W_{σ i}`: `g ⊕ id` at every node. -/
def spinTwist (σ : I ≃o I) (g : orthogonalGroup B)
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i) : TwistedAut (spinDiagram B W) :=
  ⟨σ, fun i => equivOfIsometry (pieceIsometry σ g hg i), fun _ _ => rfl⟩

theorem spinTwist_shape (σ : I ≃o I) (g : orthogonalGroup B)
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i) : (spinTwist σ g hg).shape = σ := rfl

theorem spinTwist_app_fst (σ : I ≃o I) (g : orthogonalGroup B)
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i) (i : I) (z : SpinNode B (W i)) :
    (((spinTwist σ g hg).app i z).1 : V) = (g : V ≃ₗ[R] V) z.1 := rfl

theorem spinTwist_app_snd (σ : I ≃o I) (g : orthogonalGroup B)
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i) (i : I) (z : SpinNode B (W i)) :
    ((spinTwist σ g hg).app i z).2 = z.2 := rfl

theorem spinTwist_congr {σ σ' : I ≃o I} {g g' : orthogonalGroup B}
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i)
    (hg' : ∀ i v, (g' : V ≃ₗ[R] V) v ∈ W (σ' i) ↔ v ∈ W i) (h1 : σ = σ') (h2 : g = g') :
    spinTwist σ g hg = spinTwist σ' g' hg' := by
  subst h1 h2
  rfl

theorem spinTwist_mul (σ τ : I ≃o I) (g h : orthogonalGroup B)
    (hg : ∀ i v, (g : V ≃ₗ[R] V) v ∈ W (σ i) ↔ v ∈ W i)
    (hh : ∀ i v, (h : V ≃ₗ[R] V) v ∈ W (τ i) ↔ v ∈ W i) :
    spinTwist σ g hg * spinTwist τ h hh =
      spinTwist (σ * τ) (g * h) (fun i v => (hg (τ i) _).trans (hh i v)) :=
  TwistedAut.ext' rfl fun _ _ _ => map_self _ _ _

theorem spinTwist_one : spinTwist (B := B) (W := W) 1 1 (fun _ _ => Iff.rfl) = 1 :=
  TwistedAut.ext' rfl fun _ _ _ => map_self _ _ _

end SpinTwist

/-! ### The discrete shape `P⁺ = WithTop (Disc κ)` -/

/-- `κ` with the discrete order: distinct points are incomparable. -/
def Disc (κ : Type w) : Type w := κ

instance (κ : Type w) : PartialOrder (Disc κ) where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

section Disc

variable {κ : Type w}

theorem disc_le_iff {a b : Disc κ} : a ≤ b ↔ a = b := Iff.rfl

/-- The node `k` of `P⁺ = WithTop (Disc κ)`. -/
abbrev pt (k : κ) : WithTop (Disc κ) := WithTop.some (α := Disc κ) k

/-- A permutation of `κ`, as an order automorphism of `P⁺ = WithTop (Disc κ)` fixing the top. -/
def permShape (σ : Equiv.Perm κ) : WithTop (Disc κ) ≃o WithTop (Disc κ) where
  toFun := WithTop.map (σ : Disc κ → Disc κ)
  invFun := WithTop.map (σ.symm : Disc κ → Disc κ)
  left_inv x := by
    induction x using WithTop.recTopCoe with
    | top => rfl
    | coe k => exact congrArg WithTop.some (σ.symm_apply_apply k)
  right_inv x := by
    induction x using WithTop.recTopCoe with
    | top => rfl
    | coe k => exact congrArg WithTop.some (σ.apply_symm_apply k)
  map_rel_iff' {a b} := by
    induction a using WithTop.recTopCoe with
    | top =>
      induction b using WithTop.recTopCoe with
      | top => exact Iff.rfl
      | coe k => exact ⟨fun h => absurd h (WithTop.not_top_le_coe _),
          fun h => absurd h (WithTop.not_top_le_coe _)⟩
    | coe j =>
      induction b using WithTop.recTopCoe with
      | top => exact ⟨fun _ => le_top, fun _ => le_top⟩
      | coe k =>
        exact WithTop.coe_le_coe.trans (disc_le_iff.trans (σ.injective.eq_iff.trans
          (disc_le_iff.symm.trans WithTop.coe_le_coe.symm)))

theorem permShape_coe (σ : Equiv.Perm κ) (k : κ) :
    permShape σ (pt k) = pt (σ k) := rfl

theorem permShape_top (σ : Equiv.Perm κ) : permShape σ ⊤ = ⊤ := rfl

/-- Permutations act on the shape `P⁺`. -/
def permShapeHom : Equiv.Perm κ →* (WithTop (Disc κ) ≃o WithTop (Disc κ)) where
  toFun := permShape
  map_one' := RelIso.ext fun x => by
    induction x using WithTop.recTopCoe <;> rfl
  map_mul' _ _ := RelIso.ext fun x => by
    induction x using WithTop.recTopCoe <;> rfl

theorem permShapeHom_apply (σ : Equiv.Perm κ) : permShapeHom σ = permShape σ := rfl

theorem coe_ne_top_of_orderIso (e : WithTop (Disc κ) ≃o WithTop (Disc κ)) (k : κ) :
    e (pt k) ≠ ⊤ := fun h =>
  WithTop.coe_ne_top (e.injective (h.trans e.map_top.symm))

/-- The point of `κ` that an order automorphism of `P⁺` sends `k` to. -/
def permOfOrderIso (e : WithTop (Disc κ) ≃o WithTop (Disc κ)) (k : κ) : κ :=
  (e (pt k)).untop (coe_ne_top_of_orderIso e k)

theorem coe_permOfOrderIso (e : WithTop (Disc κ) ≃o WithTop (Disc κ)) (k : κ) :
    pt (permOfOrderIso e k) = e (pt k) :=
  WithTop.coe_untop _ _

/-- **Automorphisms of `P⁺`**: every order automorphism of `WithTop (Disc κ)` is a permutation
of `κ`. -/
theorem permShape_surjective (e : WithTop (Disc κ) ≃o WithTop (Disc κ)) :
    ∃ σ : Equiv.Perm κ, permShape σ = e := by
  have hinv : ∀ (f : WithTop (Disc κ) ≃o WithTop (Disc κ)) k,
      permOfOrderIso f.symm (permOfOrderIso f k) = k := fun f k => by
    have h1 := coe_permOfOrderIso f.symm (permOfOrderIso f k)
    rw [coe_permOfOrderIso f k, OrderIso.symm_apply_apply] at h1
    exact Option.some.inj h1
  refine ⟨⟨permOfOrderIso e, permOfOrderIso e.symm, hinv e, fun k => ?_⟩, ?_⟩
  · have := hinv e.symm k
    rwa [OrderIso.symm_symm] at this
  · refine RelIso.ext fun x => ?_
    induction x using WithTop.recTopCoe with
    | top => exact e.map_top.symm
    | coe k => exact coe_permOfOrderIso e k

end Disc

/-! ### The wreath-product diagram -/

section Wreath

variable {R : Type u} [CommRing R] {U : Type u} [AddCommGroup U] [Module R U]
  (BU : LinearMap.BilinForm R U) (κ : Type u)

variable {κ} in
/-- The `k`-th copy `Uₖ` of `U` in `κ → U`: the vectors supported at `k`. -/
def piece (k : κ) : Submodule R (κ → U) where
  carrier := {v | ∀ j, j ≠ k → v j = 0}
  add_mem' {v w} hv hw j hj := by rw [Pi.add_apply, hv j hj, hw j hj, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r v hv j hj := by rw [Pi.smul_apply, hv j hj, smul_zero]

variable {κ}

theorem mem_piece_iff {k : κ} {v : κ → U} : v ∈ piece (U := U) (R := R) k ↔ ∀ j, j ≠ k → v j = 0 :=
  Iff.rfl

variable [DecidableEq κ] in
theorem single_mem_piece (k : κ) (u : U) : Pi.single k u ∈ piece (R := R) k := fun j hj => by
  rw [Pi.single_eq_of_ne hj]

variable [DecidableEq κ] in
theorem eq_single_of_mem_piece {k : κ} {v : κ → U} (hv : v ∈ piece (R := R) k) :
    v = Pi.single k (v k) := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, hv j hj]

variable (U κ) in
/-- The pieces of the wreath diagram: `Uₖ` at the node `k`, and `κ → U` at the top. -/
def wreathW : WithTop (Disc κ) →o Submodule R (κ → U) where
  toFun i := Option.elim i ⊤ fun k => piece (R := R) (U := U) (k : κ)
  monotone' a b hab := by
    induction b using WithTop.recTopCoe with
    | top => exact le_top
    | coe k =>
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (WithTop.not_top_le_coe _)
      | coe j =>
        have : j = k := WithTop.coe_le_coe.1 hab
        subst this
        exact le_rfl

theorem wreathW_coe (k : κ) :
    wreathW (R := R) U κ (pt k) = piece (R := R) k := rfl

theorem wreathW_top : wreathW (R := R) U κ ⊤ = ⊤ := rfl

variable (κ)

/-- `Perm κ` permuting the factors of `O(U)^κ`: `(σ · a)ₖ = a_{σ⁻¹ k}`. -/
def permAct : Equiv.Perm κ →* MulAut (κ → orthogonalGroup BU) where
  toFun σ :=
    { toFun := fun a k => a (σ.symm k)
      invFun := fun a k => a (σ k)
      left_inv := fun a => funext fun k => by simp
      right_inv := fun a => funext fun k => by simp
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

variable {BU κ}

theorem permAct_apply (σ : Equiv.Perm κ) (a : κ → orthogonalGroup BU) (k : κ) :
    permAct BU κ σ a k = a (σ.symm k) := rfl

/-- The isometry `v ↦ (k ↦ aₖ (v_{σ⁻¹ k}))` of `κ → U`. -/
def coordEquiv (a : κ → orthogonalGroup BU) (σ : Equiv.Perm κ) : (κ → U) ≃ₗ[R] (κ → U) where
  toFun v k := (a k : U ≃ₗ[R] U) (v (σ.symm k))
  invFun w j := (a (σ j) : U ≃ₗ[R] U).symm (w (σ j))
  map_add' v w := funext fun k => map_add _ _ _
  map_smul' r v := funext fun k => map_smul _ _ _
  left_inv v := funext fun j => by simp
  right_inv w := funext fun k => by simp

theorem coordEquiv_apply (a : κ → orthogonalGroup BU) (σ : Equiv.Perm κ) (v : κ → U) (k : κ) :
    coordEquiv a σ v k = (a k : U ≃ₗ[R] U) (v (σ.symm k)) := rfl

variable [Fintype κ]

variable (BU κ) in
/-- The orthogonal sum `B(v, w) = ∑ₖ B_U(vₖ, wₖ)` on `κ → U`. -/
def sumForm : LinearMap.BilinForm R (κ → U) :=
  ∑ k, BU.compl₁₂ (LinearMap.proj k) (LinearMap.proj k)

theorem sumForm_apply (v w : κ → U) : sumForm BU κ v w = ∑ k, BU (v k) (w k) := by
  simp only [sumForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]

instance [Fact BU.IsSymm] : Fact (sumForm BU κ).IsSymm :=
  ⟨⟨fun v w => by
    simp only [sumForm_apply]
    exact Finset.sum_congr rfl fun k _ => by simpa using (Fact.out : BU.IsSymm).eq (v k) (w k)⟩⟩

instance [Module.Free R U] : Module.Free R (wreathW (R := R) U κ ⊤) :=
  Module.Free.of_equiv (Submodule.topEquiv (R := R) (M := κ → U)).symm

/-- `coordEquiv a σ` as an element of `O(κ → U, ∑ B_U)`. -/
def coordOrth (a : κ → orthogonalGroup BU) (σ : Equiv.Perm κ) : orthogonalGroup (sumForm BU κ) :=
  ⟨coordEquiv a σ, fun v w => by
    simp only [sumForm_apply, coordEquiv_apply]
    rw [← Equiv.sum_comp σ.symm (fun j => BU (v j) (w j))]
    exact Finset.sum_congr rfl fun k _ => (a k).2 _ _⟩

theorem coordOrth_apply (a : κ → orthogonalGroup BU) (σ : Equiv.Perm κ) (v : κ → U) :
    (coordOrth a σ : (κ → U) ≃ₗ[R] (κ → U)) v = coordEquiv a σ v := rfl

theorem coordOrth_mem (a : κ → orthogonalGroup BU) (σ : Equiv.Perm κ) (i : WithTop (Disc κ))
    (v : κ → U) :
    (coordOrth a σ : (κ → U) ≃ₗ[R] (κ → U)) v ∈ wreathW (R := R) U κ (permShape σ i) ↔
      v ∈ wreathW (R := R) U κ i := by
  induction i using WithTop.recTopCoe with
  | top => exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩
  | coe k =>
    change (∀ j : κ, j ≠ σ k → (a j : U ≃ₗ[R] U) (v (σ.symm j)) = 0) ↔
      ∀ j : κ, @Ne κ j k → v j = 0
    constructor
    · intro h j hj
      have := h (σ j) (σ.injective.ne hj)
      rw [Equiv.symm_apply_apply] at this
      exact (LinearEquiv.map_eq_zero_iff _).1 this
    · intro h j hj
      rw [h (σ.symm j) (fun e => hj (by rw [← e, Equiv.apply_symm_apply])), map_zero]

theorem coordOrth_mul (x y : (κ → orthogonalGroup BU) ⋊[permAct BU κ] Equiv.Perm κ) :
    coordOrth (x * y).left (x * y).right = coordOrth x.left x.right * coordOrth y.left y.right :=
  Subtype.ext (LinearEquiv.ext fun _ => funext fun _ => rfl)

theorem coordOrth_one : coordOrth (1 : κ → orthogonalGroup BU) 1 = 1 :=
  Subtype.ext (LinearEquiv.ext fun _ => funext fun _ => rfl)

/-- An isometry of the terminal module, seen on `κ → U`. -/
def topMap (h : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤))) :
    (κ → U) →ₗ[R] (κ → U) where
  toFun v := (h.1 ⟨v, trivial⟩ : κ → U)
  map_add' v w := congrArg Subtype.val (map_add h.1 ⟨v, trivial⟩ ⟨w, trivial⟩)
  map_smul' r v := congrArg Subtype.val (map_smul h.1 r ⟨v, trivial⟩)

theorem topMap_apply (h : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤)))
    (v : κ → U) : topMap h v = (h.1 ⟨v, trivial⟩ : κ → U) :=
  rfl

theorem topMap_mem_piece {h : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤))}
    (hh : h ∈ orthStab (sumForm BU κ) (wreathW U κ)) {k : κ} {v : κ → U} :
    topMap h v ∈ piece (R := R) k ↔ v ∈ piece (R := R) k :=
  hh (pt k) ⟨v, trivial⟩

theorem topMap_mul (h h' : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤)))
    (v : κ → U) : topMap (h * h') v = topMap h (topMap h' v) := rfl

theorem topMap_one (v : κ → U) : topMap (1 : orthogonalGroup ((sumForm BU κ).restrict
    (wreathW U κ ⊤))) v = v := rfl

variable [Fact BU.IsSymm]

variable (BU κ) in
/-- The **wreath diagram**: the spin-factor diagram over `P⁺ = WithTop (Disc κ)` with the copies
`Uₖ ⊆ κ → U` at the nodes and `κ → U` at the top, for the orthogonal sum form. -/
abbrev wreathDiagram : JordanDiagram R (WithTop (Disc κ)) :=
  spinDiagram (sumForm BU κ) (wreathW U κ)

variable (BU κ) in
/-- The wreath product acting on the wreath diagram by twisted automorphisms:
`(a, σ) ↦ (σ, v ↦ (k ↦ aₖ v_{σ⁻¹ k}) ⊕ id)`. -/
def wreathHom :
    (κ → orthogonalGroup BU) ⋊[permAct BU κ] Equiv.Perm κ →* TwistedAut (wreathDiagram BU κ) where
  toFun x := spinTwist (permShape x.right) (coordOrth x.left x.right) (coordOrth_mem x.left x.right)
  map_one' := (spinTwist_congr _ _ (permShapeHom (κ := κ)).map_one coordOrth_one).trans
    spinTwist_one
  map_mul' x y := (spinTwist_congr _ _ ((permShapeHom (κ := κ)).map_mul x.right y.right)
    (coordOrth_mul x y)).trans (spinTwist_mul _ _ _ _ _ _).symm

theorem wreathHom_shape (x : (κ → orthogonalGroup BU) ⋊[permAct BU κ] Equiv.Perm κ) :
    (wreathHom BU κ x).shape = permShape x.right := rfl

theorem wreathHom_app_fst (x : (κ → orthogonalGroup BU) ⋊[permAct BU κ] Equiv.Perm κ)
    (i : WithTop (Disc κ)) (z : SpinNode (sumForm BU κ) (wreathW U κ i)) :
    (((wreathHom BU κ x).app i z).1 : κ → U) = coordEquiv x.left x.right z.1 := rfl

variable [DecidableEq κ]

omit [Fact BU.IsSymm] in
theorem sumForm_single (k : κ) (u u' : U) :
    sumForm BU κ (Pi.single k u) (Pi.single k u') = BU u u' := by
  rw [sumForm_apply, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, map_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem wreathHom_injective : Function.Injective (wreathHom BU κ) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  obtain ⟨a, σ⟩ := x
  have hσ : σ = 1 := by
    have h1 := congrArg TwistedAut.shape hx
    refine Equiv.ext fun k => ?_
    exact Option.some.inj (congrArg (fun e : WithTop (Disc κ) ≃o WithTop (Disc κ) =>
      e (pt k)) h1)
  subst hσ
  refine SemidirectProduct.ext ?_ rfl
  funext k
  refine Subtype.ext (LinearEquiv.ext fun u => ?_)
  have h2 := congrArg (fun t : TwistedAut (wreathDiagram BU κ) =>
    ((t.app (pt k)
      (SpinFactor.mk ((sumForm BU κ).restrict (wreathW U κ (pt k)))
        ⟨(Pi.single k u : κ → U), single_mem_piece k u⟩ 0)).1 : κ → U) k) hx
  change (a k : U ≃ₗ[R] U) ((Pi.single k u : κ → U) k) = (Pi.single k u : κ → U) k at h2
  rw [Pi.single_eq_same] at h2
  exact h2

/-! #### Diagram automorphisms of the wreath diagram -/

omit [Fact BU.IsSymm] in
/-- The isometry of the `k`-th copy of `U` induced by an element of the stabilizer. -/
def pieceOrth {h : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤))}
    (hh : h ∈ orthStab (sumForm BU κ) (wreathW U κ)) (k : κ) : orthogonalGroup BU :=
  have key : ∀ (g : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤))),
      g ∈ orthStab (sumForm BU κ) (wreathW U κ) →
        ∀ u, topMap g (Pi.single k u) = Pi.single k (topMap g (Pi.single k u) k) :=
    fun g hg u => eq_single_of_mem_piece ((topMap_mem_piece hg).2 (single_mem_piece k u))
  ⟨{ toFun := fun u => topMap h (Pi.single k u) k
     invFun := fun u => topMap h⁻¹ (Pi.single k u) k
     map_add' := fun u u' => by rw [Pi.single_add, map_add, Pi.add_apply]
     map_smul' := fun r u => by rw [Pi.single_smul, map_smul, Pi.smul_apply]; rfl
     left_inv := fun u => by
       change topMap h⁻¹ (Pi.single k (topMap h (Pi.single k u) k)) k = u
       rw [← key h hh u, ← topMap_mul, inv_mul_cancel, topMap_one, Pi.single_eq_same]
     right_inv := fun u => by
       change topMap h (Pi.single k (topMap h⁻¹ (Pi.single k u) k)) k = u
       rw [← key h⁻¹ ((orthStab _ _).inv_mem hh) u, ← topMap_mul, mul_inv_cancel, topMap_one,
         Pi.single_eq_same] }, fun u u' => by
    change BU (topMap h (Pi.single k u) k) (topMap h (Pi.single k u') k) = BU u u'
    rw [← sumForm_single (BU := BU) k (topMap h (Pi.single k u) k) (topMap h (Pi.single k u') k),
      ← key h hh u, ← key h hh u', ← sumForm_single (BU := BU) k u u']
    exact h.2 ⟨_, trivial⟩ ⟨_, trivial⟩⟩

omit [Fact BU.IsSymm] in
theorem topMap_eq_coordEquiv {h : orthogonalGroup ((sumForm BU κ).restrict (wreathW U κ ⊤))}
    (hh : h ∈ orthStab (sumForm BU κ) (wreathW U κ)) (v : κ → U) :
    topMap h v = coordEquiv (pieceOrth hh) 1 v := by
  have hsingle : ∀ k u, topMap h (Pi.single k u) = coordEquiv (pieceOrth hh) 1 (Pi.single k u) :=
    fun k u => by
      rw [eq_single_of_mem_piece ((topMap_mem_piece hh).2 (single_mem_piece k u))]
      funext j
      change (Pi.single k (topMap h (Pi.single k u) k) : κ → U) j =
        (pieceOrth hh j : U ≃ₗ[R] U) ((Pi.single k u : κ → U) j)
      by_cases hj : j = k
      · subst hj
        rw [Pi.single_eq_same, Pi.single_eq_same]
        rfl
      · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
  conv_lhs => rw [← Finset.univ_sum_single v]
  conv_rhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => hsingle k (v k)

variable [Invertible (2 : R)] [Module.Free R U]

/-- Every diagram automorphism of the wreath diagram comes from `O(U)^κ`. -/
theorem ofAut_eq_wreathHom (g : (wreathDiagram BU κ).autGroup) :
    ∃ a : κ → orthogonalGroup BU, TwistedAut.ofAut _ g = wreathHom BU κ ⟨a, 1⟩ := by
  have hev := autEquivOrthogonal_spinDiagramAutEquiv (sumForm BU κ) (wreathW U κ) g
  refine ⟨pieceOrth (spinDiagramAutEquiv (sumForm BU κ) (wreathW U κ) g).2,
    TwistedAut.ext' ?_ fun i z hi => ?_⟩
  · exact (permShapeHom (κ := κ)).map_one.symm
  · apply spinDiagram_ν_injective (sumForm BU κ) (wreathW U κ)
    refine ((wreathDiagram BU κ).ν_map _ _).trans ?_
    change (wreathDiagram BU κ).ν i (g.1 i z) = _
    refine (ev_ν g i z).symm.trans ?_
    refine (congrArg (fun φ : jordanAut R (wreathDiagram BU κ).J =>
      φ ((wreathDiagram BU κ).ν i z)) hev.symm).trans ?_
    refine SpinFactor.ext ((sumForm BU κ).restrict (wreathW U κ ⊤)) (Subtype.ext ?_) rfl
    exact topMap_eq_coordEquiv (spinDiagramAutEquiv (sumForm BU κ) (wreathW U κ) g).2 z.1

/-- **The wreath product**: the shape-twisted group of the wreath diagram is `O(U)^κ ⋊ Perm κ`. -/
theorem wreathHom_surjective : Function.Surjective (wreathHom BU κ) := by
  intro t
  obtain ⟨σ, hσ⟩ := permShape_surjective t.shape
  have hker : (wreathHom BU κ ⟨1, σ⟩)⁻¹ * t ∈ (TwistedAut.shapeHom _).ker := by
    change (permShape σ)⁻¹ * t.shape = 1
    rw [hσ, inv_mul_cancel]
  rw [← TwistedAut.range_ofAut] at hker
  obtain ⟨g, hg⟩ := hker
  obtain ⟨a, ha⟩ := ofAut_eq_wreathHom g
  refine ⟨⟨1, σ⟩ * ⟨a, 1⟩, ?_⟩
  rw [map_mul, ← ha, hg, mul_inv_cancel_left]

variable (BU κ) in
/-- **The wreath product**: the shape-twisted group of the wreath diagram is `O(U)^κ ⋊ Perm κ`. -/
def wreathEquiv :
    TwistedAut (wreathDiagram BU κ) ≃* (κ → orthogonalGroup BU) ⋊[permAct BU κ] Equiv.Perm κ :=
  (MulEquiv.ofBijective (wreathHom BU κ) ⟨wreathHom_injective, wreathHom_surjective⟩).symm

/-- Under `wreathEquiv`, the shape map is the permutation part. -/
theorem shapeHom_wreathEquiv_symm (x : (κ → orthogonalGroup BU) ⋊[permAct BU κ] Equiv.Perm κ) :
    TwistedAut.shapeHom _ ((wreathEquiv BU κ).symm x) = permShape x.right := rfl

theorem shapeHom_eq_permShape (t : TwistedAut (wreathDiagram BU κ)) :
    TwistedAut.shapeHom _ t = permShape (wreathEquiv BU κ t).right := by
  conv_lhs => rw [← (wreathEquiv BU κ).symm_apply_apply t]
  rfl

end Wreath

end

end JordanDiagram
