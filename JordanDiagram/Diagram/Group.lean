import JordanDiagram.Diagram.Basic

/-!
# The diagram automorphism group (Section 3.1)

`G_F(R) = Aut_{Fun(I⁺, Jord_R)}(F_R)` (Definition 3.1): families `(gᵢ)` of Jordan automorphisms
with `gⱼ ∘ F(α) = F(α) ∘ gᵢ` for every arrow `α : i ⟶ j`. Here it is `F.autGroup`, a subgroup of
the product `∀ i, jordanAut R (F.obj i)`.

* `ev`: terminal evaluation `G_F(R) → Aut(J)` (Definition 3.4).
* `ev_injective`, `range_ev`: terminal determination (Proposition 3.6). When every terminal map
  `νᵢ` is injective, `ev` is injective with image `⋂ᵢ Stab(Aᵢ)`, `Aᵢ = νᵢ(F(i))`.
* `restrictHom`: restriction along a functor `u : I' ⥤ I` (Lemma 3.11).

The paper's hypothesis is that each `νᵢ` is a monomorphism of `Jord_R`; the paper's first step
shows monomorphisms are injective, and here injectivity is taken as the hypothesis directly.
-/

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} R I)

/-- The diagram automorphism group `G_F(R)` (Definition 3.1). -/
def autGroup : Subgroup (∀ i, jordanAut R (F.obj i)) where
  carrier := {g | ∀ {i j : I} (α : i ⟶ j) (x : F.obj i), g j (F.map α x) = F.map α (g i x)}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh i j α x := by
    change g j (h j (F.map α x)) = F.map α (g i (h i x))
    rw [hh, hg]
  inv_mem' {g} hg i j α x := by
    change (g j)⁻¹ (F.map α x) = F.map α ((g i)⁻¹ x)
    apply jordanAut.injective (g j)
    rw [jordanAut.apply_inv_self, hg, jordanAut.apply_inv_self]

variable {F}

theorem mem_autGroup {g : ∀ i, jordanAut R (F.obj i)} :
    g ∈ F.autGroup ↔ ∀ {i j : I} (α : i ⟶ j) (x : F.obj i), g j (F.map α x) = F.map α (g i x) :=
  Iff.rfl

theorem autGroup_naturality (g : F.autGroup) {i j : I} (α : i ⟶ j) (x : F.obj i) :
    g.1 j (F.map α x) = F.map α (g.1 i x) :=
  g.2 α x

section Restriction

variable {I' : Type*} [Category I']

/-- Restriction `G_F(R) → Aut(F ∘ u)` along a functor `u : I' ⥤ I` (Lemma 3.11). -/
def restrictHom (u : I' ⥤ I) : F.autGroup →* (F.restrict u).autGroup where
  toFun g := ⟨fun j => g.1 (u.obj j), fun α x => g.2 (u.map α) x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem restrictHom_apply (u : I' ⥤ I) (g : F.autGroup) (j : I') :
    (restrictHom u g).1 j = g.1 (u.obj j) := rfl

end Restriction

section Terminal

variable [TerminallyPointed I]

variable (F) in
/-- Terminal evaluation `ev₊ : G_F(R) → Aut(J)` (Definition 3.4). -/
def ev : F.autGroup →* jordanAut R F.J :=
  (Pi.evalMonoidHom (fun i => jordanAut R (F.obj i)) top).comp F.autGroup.subtype

@[simp]
theorem ev_apply (g : F.autGroup) : ev F g = g.1 top := rfl

/-- The naturality equation along the terminal arrows, `g₊ ∘ νᵢ = νᵢ ∘ gᵢ`. -/
theorem ev_ν (g : F.autGroup) (i : I) (x : F.obj i) : ev F g (F.ν i x) = F.ν i (g.1 i x) :=
  g.2 (toTop i) x

/-- A diagram automorphism maps each image `Aᵢ` onto itself. -/
theorem ev_image (g : F.autGroup) (i : I) : ev F g '' F.image i = F.image i := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨g.1 i x, (ev_ν g i x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨F.ν i ((g.1 i)⁻¹ x), ⟨_, rfl⟩, ?_⟩
    rw [ev_ν, jordanAut.apply_inv_self]

variable (F) in
/-- `⋂ᵢ Stab(Aᵢ)` inside `Aut(J)`. -/
def stabImages : Subgroup (jordanAut R F.J) := ⨅ i, jordanAut.stab (F.image i)

theorem mem_stabImages {h : jordanAut R F.J} :
    h ∈ stabImages F ↔ ∀ i, h '' F.image i = F.image i := by
  simp [stabImages, Subgroup.mem_iInf, jordanAut.mem_stab]

/-- **Terminal determination**, injectivity (Proposition 3.6): when the terminal maps are
injective, a diagram automorphism is determined by its terminal component. -/
theorem ev_injective (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (ev F) := by
  intro g h hgh
  apply Subtype.ext
  funext i
  ext x
  apply hν i
  rw [← ev_ν, ← ev_ν, hgh]

/-- The diagram automorphism with terminal component `h`, for `h` stabilizing every image. -/
noncomputable def ofStab (hν : ∀ i, Function.Injective (F.ν i)) (h : jordanAut R F.J)
    (hh : h ∈ stabImages F) : F.autGroup :=
  ⟨fun i => liftAut (hν i) h (mem_stabImages.1 hh i), by
    intro i j α x
    apply hν j
    rw [liftAut_spec, F.ν_map, F.ν_map, liftAut_spec]⟩

theorem ν_ofStab (hν : ∀ i, Function.Injective (F.ν i)) (h : jordanAut R F.J)
    (hh : h ∈ stabImages F) (i : I) (x : F.obj i) :
    F.ν i ((ofStab hν h hh).1 i x) = h (F.ν i x) :=
  liftAut_spec _ _ _ _

theorem ev_ofStab (hν : ∀ i, Function.Injective (F.ν i)) (h : jordanAut R F.J)
    (hh : h ∈ stabImages F) : ev F (ofStab hν h hh) = h := by
  ext x
  have := ν_ofStab hν h hh top x
  rwa [F.ν_top, F.ν_top] at this

/-- **Terminal determination**, image (Proposition 3.6): when the terminal maps are injective,
the image of terminal evaluation is the intersection of the stabilizers of the images `Aᵢ`. -/
theorem range_ev (hν : ∀ i, Function.Injective (F.ν i)) : (ev F).range = stabImages F := by
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    exact mem_stabImages.2 (ev_image g)
  · intro hh
    exact ⟨ofStab hν h hh, ev_ofStab hν h hh⟩

/-- **Terminal determination** (Proposition 3.6): `G_F(R) ≃* ⋂ᵢ Stab(Aᵢ)`. -/
noncomputable def autGroupEquivStab (hν : ∀ i, Function.Injective (F.ν i)) :
    F.autGroup ≃* stabImages F :=
  (MonoidHom.ofInjective (ev_injective hν)).trans (MulEquiv.subgroupCongr (range_ev hν))

@[simp]
theorem autGroupEquivStab_apply (hν : ∀ i, Function.Injective (F.ν i)) (g : F.autGroup) :
    (autGroupEquivStab hν g : jordanAut R F.J) = ev F g := rfl

end Terminal

end JordanDiagram
