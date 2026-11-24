module

public import JordanDiagram.Diagram.Group
public import JordanDiagram.Diagram.Derivation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Wedges

Suppose `I⁺` is the union of two full subcategories `I₁⁺`, `I₂⁺` (given by object properties
`P₁`, `P₂`) that both contain `+`, meet only in `+`, and have no arrows between `I₁⁺ \ {+}` and
`I₂⁺ \ {+}`. The last condition, together with fullness, is recorded as: every arrow lies in
`I₁⁺` or in `I₂⁺` (`IsWedge.arrow`).

Then restriction identifies `G_F(R)` with the fiber product
`G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)` (`wedgeHom_injective`, `range_wedgeHom`, `autGroupEquivWedge`),
and likewise for compatible derivations (`wedgeDer_injective`, `range_wedgeDer`).
-/

@[expose] public section

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I] [TerminallyPointed I]

/-- The wedge hypotheses on two object properties of `I`. -/
structure IsWedge (P₁ P₂ : ObjectProperty I) : Prop where
  cover : ∀ i, P₁ i ∨ P₂ i
  top₁ : P₁ top
  top₂ : P₂ top
  inter : ∀ i, P₁ i → P₂ i → i = top
  arrow : ∀ {i j : I} (_ : i ⟶ j), (P₁ i ∧ P₁ j) ∨ (P₂ i ∧ P₂ j)

variable {F : JordanDiagram.{u, v} R I} {P₁ P₂ : ObjectProperty I}

/-- Restriction to the two halves of a wedge. -/
def wedgeHom (P₁ P₂ : ObjectProperty I) :
    F.autGroup →* (F.restrict P₁.ι).autGroup × (F.restrict P₂.ι).autGroup :=
  (restrictHom P₁.ι).prod (restrictHom P₂.ι)

/-- The two halves of a pair in the range of `wedgeHom` agree at the terminal dot. -/
def WedgeCompatible (hW : IsWedge P₁ P₂)
    (p : (F.restrict P₁.ι).autGroup × (F.restrict P₂.ι).autGroup) : Prop :=
  p.1.1 ⟨top, hW.top₁⟩ = p.2.1 ⟨top, hW.top₂⟩

theorem wedgeHom_injective (hW : IsWedge P₁ P₂) :
    Function.Injective (wedgeHom (F := F) P₁ P₂) := by
  intro g h hgh
  apply Subtype.ext
  funext i
  rcases hW.cover i with hi | hi
  · exact congrArg (fun p => p.1.1 ⟨i, hi⟩) hgh
  · exact congrArg (fun p => p.2.1 ⟨i, hi⟩) hgh

section Glue

variable (hW : IsWedge P₁ P₂) (g₁ : (F.restrict P₁.ι).autGroup) (g₂ : (F.restrict P₂.ι).autGroup)

/-- Gluing the components of a compatible pair. -/
noncomputable def wedgePick (i : I) : jordanAut R (F.obj i) := by
  classical
  exact if h : P₁ i then g₁.1 ⟨i, h⟩ else g₂.1 ⟨i, (hW.cover i).resolve_left h⟩

theorem wedgePick₁ {i : I} (h : P₁ i) : wedgePick hW g₁ g₂ i = g₁.1 ⟨i, h⟩ := by
  unfold wedgePick
  simp only [h, dite_true]

theorem wedgePick₂ (hc : WedgeCompatible hW (g₁, g₂)) {i : I} (h : P₂ i) :
    wedgePick hW g₁ g₂ i = g₂.1 ⟨i, h⟩ := by
  classical
  by_cases h₁ : P₁ i
  · obtain rfl := hW.inter i h₁ h
    rw [wedgePick₁ hW g₁ g₂ h₁]
    exact hc
  · unfold wedgePick
    simp only [h₁, dite_false]

/-- The diagram automorphism glued from a compatible pair. -/
noncomputable def wedgeGlue (hc : WedgeCompatible hW (g₁, g₂)) : F.autGroup :=
  ⟨wedgePick hW g₁ g₂, by
    intro i j α x
    rcases hW.arrow α with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [wedgePick₁ hW g₁ g₂ hi, wedgePick₁ hW g₁ g₂ hj]
      exact autGroup_naturality g₁
        (ObjectProperty.homMk (X := (⟨i, hi⟩ : P₁.FullSubcategory)) (Y := ⟨j, hj⟩) α) x
    · rw [wedgePick₂ hW g₁ g₂ hc hi, wedgePick₂ hW g₁ g₂ hc hj]
      exact autGroup_naturality g₂
        (ObjectProperty.homMk (X := (⟨i, hi⟩ : P₂.FullSubcategory)) (Y := ⟨j, hj⟩) α) x⟩

theorem wedgeHom_wedgeGlue (hc : WedgeCompatible hW (g₁, g₂)) :
    wedgeHom P₁ P₂ (wedgeGlue hW g₁ g₂ hc) = (g₁, g₂) := by
  ext ⟨i, hi⟩ x
  · exact congrArg (fun a : jordanAut R (F.obj i) => a x) (wedgePick₁ hW g₁ g₂ hi)
  · exact congrArg (fun a : jordanAut R (F.obj i) => a x) (wedgePick₂ hW g₁ g₂ hc hi)

end Glue

/-- **Wedge decomposition** (groups): the image of restriction to the two halves of a wedge is the
fiber product over `Aut(J)`. -/
theorem range_wedgeHom (hW : IsWedge P₁ P₂) :
    Set.range (wedgeHom (F := F) P₁ P₂) = {p | WedgeCompatible hW p} := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    rfl
  · intro hc
    exact ⟨wedgeGlue hW p.1 p.2 hc, wedgeHom_wedgeGlue hW p.1 p.2 hc⟩

/-- The fiber product `G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)` as a subgroup. -/
def wedgeFiberProduct (hW : IsWedge P₁ P₂) :
    Subgroup ((F.restrict P₁.ι).autGroup × (F.restrict P₂.ι).autGroup) where
  carrier := {p | WedgeCompatible hW p}
  one_mem' := rfl
  mul_mem' hp hq :=
    congrArg₂ (fun a b : jordanAut R (F.obj top) => a * b) hp hq
  inv_mem' hp := congrArg (fun a : jordanAut R (F.obj top) => a⁻¹) hp

/-- **Wedge decomposition** (groups): `G_F(R) ≃* G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)`. -/
noncomputable def autGroupEquivWedge (hW : IsWedge P₁ P₂) :
    F.autGroup ≃* wedgeFiberProduct (F := F) hW :=
  (MonoidHom.ofInjective (wedgeHom_injective hW)).trans
    (MulEquiv.subgroupCongr (by
      ext p
      change p ∈ Set.range (wedgeHom P₁ P₂) ↔ _
      rw [range_wedgeHom hW]
      rfl))

section Der

/-- Restriction of compatible derivations to the two halves of a wedge. -/
def wedgeDer (P₁ P₂ : ObjectProperty I) (D : F.derAlgebra) :
    (F.restrict P₁.ι).derAlgebra × (F.restrict P₂.ι).derAlgebra :=
  (restrictDer P₁.ι D, restrictDer P₂.ι D)

theorem wedgeDer_injective (hW : IsWedge P₁ P₂) :
    Function.Injective (wedgeDer (F := F) P₁ P₂) := by
  intro D E hDE
  apply Subtype.ext
  funext i
  rcases hW.cover i with hi | hi
  · exact congrArg (fun p => p.1.1 ⟨i, hi⟩) hDE
  · exact congrArg (fun p => p.2.1 ⟨i, hi⟩) hDE

variable (hW : IsWedge P₁ P₂) (D₁ : (F.restrict P₁.ι).derAlgebra)
  (D₂ : (F.restrict P₂.ι).derAlgebra)

/-- Gluing the components of a compatible pair of derivation families. -/
noncomputable def wedgePickDer (i : I) : JordanDerivation R (F.obj i) := by
  classical
  exact if h : P₁ i then D₁.1 ⟨i, h⟩ else D₂.1 ⟨i, (hW.cover i).resolve_left h⟩

theorem wedgePickDer₁ {i : I} (h : P₁ i) : wedgePickDer hW D₁ D₂ i = D₁.1 ⟨i, h⟩ := by
  unfold wedgePickDer
  simp only [h, dite_true]

theorem wedgePickDer₂ (hc : D₁.1 ⟨top, hW.top₁⟩ = D₂.1 ⟨top, hW.top₂⟩) {i : I} (h : P₂ i) :
    wedgePickDer hW D₁ D₂ i = D₂.1 ⟨i, h⟩ := by
  classical
  by_cases h₁ : P₁ i
  · obtain rfl := hW.inter i h₁ h
    rw [wedgePickDer₁ hW D₁ D₂ h₁]
    exact hc
  · unfold wedgePickDer
    simp only [h₁, dite_false]

/-- **Wedge decomposition** (derivations): the image of restriction to the two halves of a wedge is
the fiber product over `Der(J)`. -/
theorem range_wedgeDer :
    Set.range (wedgeDer (F := F) P₁ P₂) =
      {p | p.1.1 ⟨top, hW.top₁⟩ = p.2.1 ⟨top, hW.top₂⟩} := by
  ext ⟨D₁, D₂⟩
  constructor
  · rintro ⟨D, hD⟩
    rw [← hD]
    rfl
  · intro hc
    refine ⟨⟨wedgePickDer hW D₁ D₂, ?_⟩, ?_⟩
    · intro i j α x
      rcases hW.arrow α with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [wedgePickDer₁ hW D₁ D₂ hi, wedgePickDer₁ hW D₁ D₂ hj]
        exact (mem_derAlgebra.1 D₁.2)
          (ObjectProperty.homMk (X := (⟨i, hi⟩ : P₁.FullSubcategory)) (Y := ⟨j, hj⟩) α) x
      · rw [wedgePickDer₂ hW D₁ D₂ hc hi, wedgePickDer₂ hW D₁ D₂ hc hj]
        exact (mem_derAlgebra.1 D₂.2)
          (ObjectProperty.homMk (X := (⟨i, hi⟩ : P₂.FullSubcategory)) (Y := ⟨j, hj⟩) α) x
    · ext ⟨i, hi⟩ x
      · exact congrArg (fun d : JordanDerivation R (F.obj i) => d x) (wedgePickDer₁ hW D₁ D₂ hi)
      · exact congrArg (fun d : JordanDerivation R (F.obj i) => d x)
          (wedgePickDer₂ hW D₁ D₂ hc hi)

end Der

end JordanDiagram
