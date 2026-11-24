module

public import JordanDiagram.Diagram.Group
public import JordanDiagram.Algebra.Equiv

/-!
# Isomorphisms of diagrams and shape-twisted automorphisms

`DiagramIso F F'`: natural isomorphisms between two diagrams over the same indexing category, i.e.
the isomorphisms in the fiber of the Grothendieck construction over `(I⁺, R)`.

* `DiagramIso.terminalEquiv`: **terminal determination for isomorphisms**. When the terminal maps
  of both diagrams are injective, an isomorphism `F ≅ F'` is the same as a Jordan isomorphism
  `h : J ≃ⱼ J'` with `h(Aᵢ) = A'ᵢ` for every `i`. The same argument gives terminal determination for
  automorphisms, for twisted automorphisms, and for isomorphisms of spin-factor diagrams.
* `TwistedIso F u`: for an endofunctor `u` of `I⁺`, an isomorphism `F ≅ u* F = F ∘ u`. For
  `u ∈ Aut(I⁺, +)` these are the elements of the shape-twisted group `G̃_F(R)` lying over `u`.
  `twistedTerminalEquiv` is **terminal determination for twisted automorphisms**: such
  a `θ` is determined by its terminal component, which may be any Jordan isomorphism
  `h : F(+) ≃ⱼ F(u +)` with `h(Aᵢ) = νᵘᵢ(F(u i))`. For `u = 𝟭`, twisted isomorphisms are
  the diagram automorphisms (`twistedIdEquiv`), which gives the kernel of `G̃_F(R) → Aut(I⁺, +)`.
-/

@[expose] public section

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]

/-- A natural isomorphism of Jordan diagrams over the same indexing category. -/
structure DiagramIso (F F' : JordanDiagram.{u, v} R I) where
  /-- The component at node `i`. -/
  app : ∀ i, F.obj i ≃ⱼ[R] F'.obj i
  naturality : ∀ {i j : I} (α : i ⟶ j) (x : F.obj i), app j (F.map α x) = F'.map α (app i x)

namespace DiagramIso

variable {F F' F'' : JordanDiagram.{u, v} R I}

@[ext]
theorem ext {θ θ' : DiagramIso F F'} (h : ∀ i x, θ.app i x = θ'.app i x) : θ = θ' := by
  obtain ⟨θ, _⟩ := θ
  obtain ⟨θ', _⟩ := θ'
  congr
  funext i
  exact JordanEquiv.ext (h i)

/-- The identity isomorphism. -/
def refl (F : JordanDiagram.{u, v} R I) : DiagramIso F F :=
  ⟨fun i => JordanEquiv.refl R (F.obj i), fun _ _ => rfl⟩

/-- The inverse isomorphism. -/
def symm (θ : DiagramIso F F') : DiagramIso F' F :=
  ⟨fun i => (θ.app i).symm, fun α x => by
    apply (θ.app _).injective
    rw [JordanEquiv.apply_symm_apply, θ.naturality, JordanEquiv.apply_symm_apply]⟩

/-- Composition of isomorphisms. -/
def trans (θ : DiagramIso F F') (θ' : DiagramIso F' F'') : DiagramIso F F'' :=
  ⟨fun i => (θ.app i).trans (θ'.app i), fun α x => by
    simp only [JordanEquiv.trans_apply, θ.naturality, θ'.naturality]⟩

/-- The diagram automorphism group is the group of self-isomorphisms. -/
def autEquiv (F : JordanDiagram.{u, v} R I) : DiagramIso F F ≃ F.autGroup where
  toFun θ := ⟨fun i => (θ.app i).toAut, fun α x => θ.naturality α x⟩
  invFun g := ⟨fun i => JordanEquiv.ofAut (g.1 i), fun α x => g.2 α x⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Terminal

variable [TerminallyPointed I]

/-- An isomorphism of diagrams maps each image `Aᵢ ⊆ J` onto `A'ᵢ ⊆ J'`. -/
theorem app_top_image (θ : DiagramIso F F') (i : I) :
    θ.app top '' F.image i = F'.image i := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨θ.app i x, (θ.naturality (toTop i) x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨F.ν i ((θ.app i).symm x), ⟨_, rfl⟩, ?_⟩
    change θ.app top (F.map (toTop i) _) = F'.map (toTop i) x
    rw [θ.naturality, JordanEquiv.apply_symm_apply]

variable (hν : ∀ i, Function.Injective (F.ν i)) (hν' : ∀ i, Function.Injective (F'.ν i))

/-- The isomorphism of diagrams with terminal component `h`, for `h(Aᵢ) = A'ᵢ`. -/
noncomputable def ofTerminal (h : F.J ≃ⱼ[R] F'.J) (hh : ∀ i, h '' F.image i = F'.image i) :
    DiagramIso F F' :=
  ⟨fun i => JordanEquiv.lift (hν i) (hν' i) h (hh i), by
    intro i j α x
    apply hν' j
    rw [JordanEquiv.lift_spec, F.ν_map, F'.ν_map, JordanEquiv.lift_spec]⟩

theorem ofTerminal_app_top (h : F.J ≃ⱼ[R] F'.J) (hh : ∀ i, h '' F.image i = F'.image i) :
    (ofTerminal hν hν' h hh).app top = h := by
  ext x
  have := JordanEquiv.lift_spec (hν top) (hν' top) h (hh top) x
  rwa [F.ν_top, F'.ν_top] at this

/-- **Terminal determination for isomorphisms**: when the terminal maps of `F` and `F'` are
injective, isomorphisms `F ≅ F'` correspond to Jordan isomorphisms `J ≃ⱼ J'` carrying every
`Aᵢ` onto `A'ᵢ`. -/
noncomputable def terminalEquiv :
    DiagramIso F F' ≃ {h : F.J ≃ⱼ[R] F'.J // ∀ i, h '' F.image i = F'.image i} where
  toFun θ := ⟨θ.app top, app_top_image θ⟩
  invFun h := ofTerminal hν hν' h.1 h.2
  left_inv θ := by
    ext i x
    apply hν' i
    exact (JordanEquiv.lift_spec (hν i) (hν' i) (θ.app top) (app_top_image θ i) x).trans
      (θ.naturality (toTop i) x)
  right_inv h := Subtype.ext (ofTerminal_app_top hν hν' h.1 h.2)

end Terminal

end DiagramIso

section Twisted

variable (F : JordanDiagram.{u, v} R I)

/-- For an endofunctor `u` of the shape, a *twisted automorphism over `u`* is an isomorphism
`F ≅ u* F`: Jordan isomorphisms `θᵢ : F(i) ≃ F(u i)` with
`θⱼ ∘ F(α) = F(u α) ∘ θᵢ`. -/
abbrev TwistedIso (u : I ⥤ I) := DiagramIso F (F.restrict u)

/-- Twisted isomorphisms over the identity are the diagram automorphisms: the kernel of
`G̃_F(R) → Aut(I⁺, +)` is `G_F(R)`. -/
def twistedIdEquiv : TwistedIso F (𝟭 I) ≃ F.autGroup := DiagramIso.autEquiv F

variable [TerminallyPointed I] {F}

/-- **Terminal determination for twisted automorphisms**: if the terminal maps of `F` and of
`u* F` are injective, a twisted automorphism over `u` is determined by its terminal component
`θ₊ : F(+) ≃ⱼ F(u +)`, which may be any Jordan isomorphism carrying `Aᵢ` onto the image of
`F(u i) → F(u +)`. -/
noncomputable def twistedTerminalEquiv (u : I ⥤ I) (hν : ∀ i, Function.Injective (F.ν i))
    (hν' : ∀ i, Function.Injective ((F.restrict u).ν i)) :
    TwistedIso F u ≃
      {h : F.J ≃ⱼ[R] F.obj (u.obj top) // ∀ i, h '' F.image i = (F.restrict u).image i} :=
  DiagramIso.terminalEquiv hν hν'

/-- The terminal maps `F(u i) → F(u +)` of `u* F` are injective when those of `F` are: composing
with the terminal map `F(u +) → F(+)` gives the injective terminal map of `u i`. -/
theorem restrict_ν_injective (u : I ⥤ I) (hν : ∀ i, Function.Injective (F.ν i)) (i : I) :
    Function.Injective ((F.restrict u).ν i) := by
  intro x y hxy
  apply hν (u.obj i)
  have hx := F.ν_map (u.map (toTop i)) x
  have hy := F.ν_map (u.map (toTop i)) y
  change F.ν (u.obj top) ((F.restrict u).ν i x) = _ at hx
  change F.ν (u.obj top) ((F.restrict u).ν i y) = _ at hy
  rw [← hx, ← hy, hxy]

end Twisted

end JordanDiagram
