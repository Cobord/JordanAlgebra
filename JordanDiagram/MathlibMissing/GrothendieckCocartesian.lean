module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# The covariant Grothendieck construction is an opfibration

For a pseudofunctor `F : 𝒮 → Cat` (covariant, on `LocallyDiscrete 𝒮`), the projection
`forget F : ∫ F ⥤ 𝒮` has strongly cocartesian lifts: for `a = (R, x)` and `f : R ⟶ S` the arrow
`(f, 𝟙) : (R, x) ⟶ (S, F(f) x)` is strongly cocartesian (`isStronglyCocartesian_cocartesianLift`).
This is the dual of Mathlib's `CoGrothendieck.isStronglyCartesian_homCartesianLift`, for which
Mathlib gives the `IsFibered` instance; Mathlib has no class of opfibrations, so the result is
stated as the existence of strongly cocartesian lifts (`exists_isStronglyCocartesian`).
-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor.Grothendieck

open CategoryTheory.Functor Bicategory

variable {𝒮 : Type*} [Category* 𝒮] {F : LocallyDiscrete 𝒮 ⥤ᵖ Cat}

section

variable (a : ∫ F) {S : 𝒮} (f : a.base ⟶ S)

/-- The codomain of the cocartesian lift of `f`. -/
abbrev codomainCocartesianLift : ∫ F := ⟨S, (F.map f.toLoc).toFunctor.obj a.fiber⟩

/-- The cocartesian lift of `f`. -/
abbrev cocartesianLift : a ⟶ codomainCocartesianLift a f := ⟨f, 𝟙 _⟩

instance isHomLift_cocartesianLift : IsHomLift (forget F) f (cocartesianLift a f) :=
  IsHomLift.map (forget F) (cocartesianLift a f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {a} in
/-- Given a lift `φ'` of `f ≫ g`, the canonical map from the codomain of the cocartesian lift of
`f` to the codomain of `φ'`. -/
abbrev homCocartesianLift {b' : ∫ F} (g : S ⟶ b'.1) (φ' : a ⟶ b')
    [IsHomLift (forget F) (f ≫ g) φ'] : codomainCocartesianLift a f ⟶ b' where
  base := g
  fiber :=
    have : φ'.base = f ≫ g := by simpa using IsHomLift.fac' (forget F) (f ≫ g) φ'
    (F.mapComp f.toLoc g.toLoc).inv.toNatTrans.app a.fiber ≫ eqToHom (by simp [this]) ≫
      φ'.fiber

instance isHomLift_homCocartesianLift {b' : ∫ F} {φ' : a ⟶ b'} {g : S ⟶ b'.1}
    [IsHomLift (forget F) (f ≫ g) φ'] : IsHomLift (forget F) g (homCocartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCocartesianLift f g φ')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The canonical lift `(f, 𝟙) : (R, x) ⟶ (S, F(f) x)` is strongly cocartesian.** -/
lemma isStronglyCocartesian_cocartesianLift :
    IsStronglyCocartesian (forget F) f (cocartesianLift a f) where
  universal_property' {b'} g φ' hφ' := by
    refine ⟨homCocartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (f ≫ g) φ') (by simp)
    rintro χ' ⟨hχ', rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp

end

/-- **`forget F : ∫ F ⥤ 𝒮` is an opfibration**: every arrow of `𝒮` out of the image of an object
has a strongly cocartesian lift. -/
theorem exists_isStronglyCocartesian (a : ∫ F) {S : 𝒮} (f : a.base ⟶ S) :
    ∃ (b : ∫ F) (φ : a ⟶ b), IsStronglyCocartesian (forget F) f φ :=
  ⟨_, _, isStronglyCocartesian_cocartesianLift a f⟩

end CategoryTheory.Pseudofunctor.Grothendieck
