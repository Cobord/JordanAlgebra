module

public import JordanDiagram.Algebra.SpinFactor
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection

/-!
# Orthogonal splittings and stabilizers (automorphisms of spin-factor flags)

Let `B` be a symmetric bilinear form on an `R`-module `V`, and `W ⊆ V` a submodule on which `B`
is *nonsingular*: `w ↦ B(w, ·)|_W` identifies `W` with its dual (`IsNonsingularOn`). Then:

* `isCompl_orthogonal`: `V = W ⊕ W⊥`. Every `v` has a unique `w ∈ W` with
  `B(v, ·)|_W = B(w, ·)|_W`, and `v - w ∈ W⊥`.
* `stabEquivProd`: the stabilizer of `W` in `O(V, B)(R)` is `O(W, B) × O(W⊥, B)`, by
  restriction to the two pieces; an isometry preserving `W` also preserves `W⊥`.

This is the one-member case of the description of automorphism groups of nonsingular spin-factor
flags. Together with the identification of a spin-factor diagram's automorphism group with a
stabilizer in the orthogonal group (`spinDiagramAutEquiv`), it says the automorphism group of the
spin-factor diagram `J(W, B) ↪ J(V, B)` is `O(W) × O(W⊥)`. Iterating over a flag gives a product
`∏ⱼ O(Uⱼ)`.
-/

@[expose] public section

open LinearMap (BilinForm)

namespace SpinFactor

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (B : LinearMap.BilinForm R V) (W : Submodule R V)

/-- `B` is nonsingular on `W`: `w ↦ B(w, ·)|_W` is a bijection `W → W*`. -/
def IsNonsingularOn : Prop := Function.Bijective (B.restrict W)

variable {B W}

/-- **Orthogonal splitting**: a symmetric form nonsingular on `W` gives `V = W ⊕ W⊥`. -/
theorem isCompl_orthogonal (hB : B.IsSymm) (hW : IsNonsingularOn B W) :
    IsCompl W (B.orthogonal W) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : B.restrict W ⟨x, hx⟩ = B.restrict W 0 := by
      ext w
      simp only [LinearMap.BilinForm.restrict_apply, map_zero, LinearMap.zero_apply]
      change B x w = 0
      rw [hB.eq]
      exact hx' w w.2
    exact congrArg Subtype.val (hW.1 h0)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    obtain ⟨w, hw⟩ := hW.2 ((B v).comp W.subtype)
    refine Submodule.mem_sup.2 ⟨w, w.2, v - w, ?_, add_sub_cancel _ _⟩
    intro n hn
    have := LinearMap.congr_fun hw ⟨n, hn⟩
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at this
    change B (w : V) n = B v n at this
    change B n (v - w) = 0
    rw [map_sub, hB.eq n v, hB.eq n w, this, sub_self]

section Restrict

/-- The restriction of a linear automorphism `g` with `g v ∈ P ↔ v ∈ P` to `P`. -/
def restrictEquiv (g : V ≃ₗ[R] V) (P : Submodule R V) (h : ∀ v, g v ∈ P ↔ v ∈ P) :
    P ≃ₗ[R] P :=
  g.ofSubmodules P P (by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨g.symm v, (h _).1 ?_, g.apply_symm_apply v⟩
      rwa [g.apply_symm_apply])

@[simp]
theorem coe_restrictEquiv (g : V ≃ₗ[R] V) (P : Submodule R V) (h : ∀ v, g v ∈ P ↔ v ∈ P)
    (x : P) : (restrictEquiv g P h x : V) = g x := rfl

end Restrict

variable (B W) in
/-- The stabilizer of `W` in `O(V, B)(R)`. -/
def stabSub : Subgroup (orthogonalGroup B) where
  carrier := {g | ∀ v, (g : V ≃ₗ[R] V) v ∈ W ↔ v ∈ W}
  one_mem' _ := Iff.rfl
  mul_mem' {g h} hg hh v := by
    change (g : V ≃ₗ[R] V) ((h : V ≃ₗ[R] V) v) ∈ W ↔ _
    rw [hg, hh]
  inv_mem' {g} hg v := by
    change (g : V ≃ₗ[R] V).symm v ∈ W ↔ _
    rw [← hg, LinearEquiv.apply_symm_apply]

/-- An isometry preserving `W` preserves `W⊥`. -/
theorem stabSub_orthogonal (_hB : B.IsSymm) (g : stabSub B W) (u : V) :
    (g.1 : V ≃ₗ[R] V) u ∈ B.orthogonal W ↔ u ∈ B.orthogonal W := by
  have key : ∀ h : stabSub B W, ∀ u ∈ B.orthogonal W, (h.1 : V ≃ₗ[R] V) u ∈ B.orthogonal W := by
    intro h u hu n hn
    change B n ((h.1 : V ≃ₗ[R] V) u) = 0
    have hn' : (h.1 : V ≃ₗ[R] V).symm n ∈ W := by
      rw [← h.2, LinearEquiv.apply_symm_apply]
      exact hn
    rw [← (h.1 : V ≃ₗ[R] V).apply_symm_apply n, h.1.2]
    exact hu _ hn'
  refine ⟨fun hu => ?_, key g u⟩
  have := key g⁻¹ _ hu
  rwa [show ((g⁻¹ : stabSub B W).1 : V ≃ₗ[R] V) ((g.1 : V ≃ₗ[R] V) u) = u from
    (g.1 : V ≃ₗ[R] V).symm_apply_apply u] at this

/-- The isometry of `(P, B|_P)` restricted from an isometry preserving `P`. -/
def restrictOrth (g : orthogonalGroup B) (P : Submodule R V)
    (h : ∀ v, (g : V ≃ₗ[R] V) v ∈ P ↔ v ∈ P) : orthogonalGroup (B.restrict P) :=
  ⟨restrictEquiv g P h, fun x y => by
    simp only [LinearMap.BilinForm.restrict_apply, coe_restrictEquiv]
    exact g.2 x y⟩

variable (hB : B.IsSymm)

/-- Restriction to `W` and `W⊥`, as a group homomorphism. -/
def stabToProd :
    stabSub B W →* orthogonalGroup (B.restrict W) × orthogonalGroup (B.restrict (B.orthogonal W)) where
  toFun g := (restrictOrth g.1 W g.2, restrictOrth g.1 _ (stabSub_orthogonal hB g))
  map_one' := rfl
  map_mul' _ _ := rfl

variable (hW : IsNonsingularOn B W)

include hW in
theorem stabToProd_injective : Function.Injective (stabToProd (W := W) hB) := by
  intro g h hgh
  have h1 := congrArg Prod.fst hgh
  have h2 := congrArg Prod.snd hgh
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine (LinearMap.ofIsCompl_eq (isCompl_orthogonal hB hW) (χ := (g.1.1 : V →ₗ[R] V))
    (φ := (g.1.1 : V →ₗ[R] V) ∘ₗ W.subtype) (ψ := (g.1.1 : V →ₗ[R] V) ∘ₗ (B.orthogonal W).subtype)
    (fun _ => rfl) (fun _ => rfl)).symm.trans
    (LinearMap.ofIsCompl_eq (isCompl_orthogonal hB hW) (fun u => ?_) (fun u => ?_))
  · exact congrArg (fun k : orthogonalGroup (B.restrict W) => ((k.1 u : W) : V)) h1
  · exact congrArg (fun k : orthogonalGroup (B.restrict (B.orthogonal W)) =>
      ((k.1 u : B.orthogonal W) : V)) h2

section Glue

variable (g₁ : orthogonalGroup (B.restrict W)) (g₂ : orthogonalGroup (B.restrict (B.orthogonal W)))

/-- The linear map `g₁ ⊕ g₂ : V → V`. -/
noncomputable def glue (e₁ : W ≃ₗ[R] W) (e₂ : B.orthogonal W ≃ₗ[R] B.orthogonal W) :
    V →ₗ[R] V :=
  LinearMap.ofIsCompl (isCompl_orthogonal hB hW) (W.subtype ∘ₗ e₁.toLinearMap)
    ((B.orthogonal W).subtype ∘ₗ e₂.toLinearMap)

theorem glue_left (e₁ : W ≃ₗ[R] W) (e₂ : B.orthogonal W ≃ₗ[R] B.orthogonal W) (u : W) :
    glue hB hW e₁ e₂ u = e₁ u := LinearMap.ofIsCompl_apply_left _ u

theorem glue_right (e₁ : W ≃ₗ[R] W) (e₂ : B.orthogonal W ≃ₗ[R] B.orthogonal W)
    (u : B.orthogonal W) : glue hB hW e₁ e₂ u = e₂ u := LinearMap.ofIsCompl_apply_right _ u

theorem glue_comp (e₁ e₁' : W ≃ₗ[R] W) (e₂ e₂' : B.orthogonal W ≃ₗ[R] B.orthogonal W) :
    glue hB hW e₁ e₂ ∘ₗ glue hB hW e₁' e₂' = glue hB hW (e₁'.trans e₁) (e₂'.trans e₂) := by
  refine (LinearMap.ofIsCompl_eq (isCompl_orthogonal hB hW) (fun u => ?_) (fun u => ?_)).symm
  · simp only [LinearMap.comp_apply, glue_left]
    rfl
  · simp only [LinearMap.comp_apply, glue_right]
    rfl

theorem glue_refl : glue hB hW (LinearEquiv.refl R W) (LinearEquiv.refl R (B.orthogonal W)) =
    LinearMap.id :=
  LinearMap.ofIsCompl_eq (isCompl_orthogonal hB hW) (fun _ => rfl) (fun _ => rfl)

/-- The linear automorphism `g₁ ⊕ g₂` of `V`. -/
noncomputable def glueEquiv (e₁ : W ≃ₗ[R] W) (e₂ : B.orthogonal W ≃ₗ[R] B.orthogonal W) :
    V ≃ₗ[R] V :=
  LinearEquiv.ofLinearMap (glue hB hW e₁ e₂) (glue hB hW e₁.symm e₂.symm)
    (by rw [glue_comp]; simp only [LinearEquiv.symm_trans_self]; exact glue_refl hB hW)
    (by rw [glue_comp]; simp only [LinearEquiv.self_trans_symm]; exact glue_refl hB hW)

include hB hW in
theorem exists_decomp (v : V) : ∃ a ∈ W, ∃ b ∈ B.orthogonal W, a + b = v :=
  Submodule.mem_sup.1 ((codisjoint_iff.1 (isCompl_orthogonal hB hW).2).symm ▸ trivial)

theorem glueEquiv_isometry (v v' : V) :
    B (glueEquiv hB hW g₁.1 g₂.1 v) (glueEquiv hB hW g₁.1 g₂.1 v') = B v v' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hB hW v
  obtain ⟨a', ha', b', hb', rfl⟩ := exists_decomp hB hW v'
  have e : ∀ x y, glueEquiv hB hW g₁.1 g₂.1 (x + y) = glue hB hW g₁.1 g₂.1 x +
      glue hB hW g₁.1 g₂.1 y := fun x y => map_add (glue hB hW g₁.1 g₂.1) x y
  rw [e, e]
  have la := glue_left hB hW g₁.1 g₂.1 ⟨a, ha⟩
  have la' := glue_left hB hW g₁.1 g₂.1 ⟨a', ha'⟩
  have rb := glue_right hB hW g₁.1 g₂.1 ⟨b, hb⟩
  have rb' := glue_right hB hW g₁.1 g₂.1 ⟨b', hb'⟩
  simp only at la la' rb rb'
  rw [la, la', rb, rb']
  -- cross terms vanish: `W ⊥ W⊥`
  have o1 : ∀ x ∈ W, ∀ y ∈ B.orthogonal W, B x y = 0 := fun x hx y hy => hy x hx
  have o2 : ∀ x ∈ B.orthogonal W, ∀ y ∈ W, B x y = 0 := fun x hx y hy => by
    rw [hB.eq]; exact hx y hy
  simp only [map_add, LinearMap.add_apply]
  rw [o1 _ (g₁.1 ⟨a, ha⟩).2 _ (g₂.1 ⟨b', hb'⟩).2, o2 _ (g₂.1 ⟨b, hb⟩).2 _ (g₁.1 ⟨a', ha'⟩).2,
    o1 a ha b' hb', o2 b hb a' ha']
  have i1 : B (g₁.1 ⟨a, ha⟩ : V) (g₁.1 ⟨a', ha'⟩) = B a a' := g₁.2 ⟨a, ha⟩ ⟨a', ha'⟩
  have i2 : B (g₂.1 ⟨b, hb⟩ : V) (g₂.1 ⟨b', hb'⟩) = B b b' := g₂.2 ⟨b, hb⟩ ⟨b', hb'⟩
  rw [i1, i2]

theorem glueEquiv_mem_iff (v : V) : glueEquiv hB hW g₁.1 g₂.1 v ∈ W ↔ v ∈ W := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hB hW v
  have hc := isCompl_orthogonal hB hW
  change glue hB hW g₁.1 g₂.1 (a + b) ∈ W ↔ _
  rw [map_add]
  have la := glue_left hB hW g₁.1 g₂.1 ⟨a, ha⟩
  have rb := glue_right hB hW g₁.1 g₂.1 ⟨b, hb⟩
  simp only at la rb
  rw [la, rb, Submodule.add_mem_iff_right _ (g₁.1 ⟨a, ha⟩).2, Submodule.add_mem_iff_right _ ha]
  constructor
  · intro h
    have h0 : ((g₂.1 ⟨b, hb⟩ : B.orthogonal W) : V) = 0 :=
      (Submodule.disjoint_def.1 hc.1) _ h (g₂.1 ⟨b, hb⟩).2
    have : g₂.1 ⟨b, hb⟩ = 0 := Subtype.ext h0
    rw [LinearEquiv.map_eq_zero_iff] at this
    rw [show b = 0 from congrArg Subtype.val this]
    exact W.zero_mem
  · intro h
    obtain rfl : b = 0 := (Submodule.disjoint_def.1 hc.1) _ h hb
    have h0 : (⟨0, hb⟩ : B.orthogonal W) = 0 := rfl
    rw [h0, map_zero]
    exact W.zero_mem

/-- The element `g₁ ⊕ g₂` of the stabilizer. -/
noncomputable def glueStab : stabSub B W :=
  ⟨⟨glueEquiv hB hW g₁.1 g₂.1, glueEquiv_isometry hB hW g₁ g₂⟩, glueEquiv_mem_iff hB hW g₁ g₂⟩

theorem stabToProd_glueStab : stabToProd hB (glueStab hB hW g₁ g₂) = (g₁, g₂) := by
  ext u
  · exact glue_left hB hW g₁.1 g₂.1 u
  · exact glue_right hB hW g₁.1 g₂.1 u

end Glue

/-- **Stabilizer of a nonsingular submodule**: the stabilizer of `W` in `O(V, B)(R)` is
`O(W, B) × O(W⊥, B)`, by restriction. -/
noncomputable def stabEquivProd :
    stabSub B W ≃* orthogonalGroup (B.restrict W) × orthogonalGroup (B.restrict (B.orthogonal W)) :=
  MulEquiv.ofBijective (stabToProd hB) ⟨stabToProd_injective hB hW,
    fun p => ⟨glueStab hB hW p.1 p.2, stabToProd_glueStab hB hW p.1 p.2⟩⟩

end SpinFactor
