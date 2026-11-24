import Mathlib.Algebra.Lie.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# Lie ring homomorphisms and the category of Lie rings

Mathlib has Lie algebra homomorphisms `L →ₗ⁅R⁆ L'` over a commutative ring `R`, but no notion of
a homomorphism of Lie rings and no category of Lie rings.

* `LieRingHom L L'` (notation `L →⁅⁆ L'`): an additive map preserving the bracket. The bracket
  preservation `map_lie'` is a field of the structure.
* `LieRingCat`: the category whose objects are Lie rings and whose morphisms are Lie ring
  homomorphisms. The API follows `GrpCat`: `LieRingCat.of`, `LieRingCat.ofHom`, `Hom.hom`,
  `hom_ext`, and a `ConcreteCategory` instance.

This is the target of the compatible-derivation functor `g_F : CAlg_R → LieRing` of
Proposition 3.8 (`JordanDiagram.derFunctor`). It is generic and could be upstreamed.
-/

universe u

open CategoryTheory

/-- A homomorphism of Lie rings: an additive map preserving the bracket. -/
structure LieRingHom (L L' : Type*) [LieRing L] [LieRing L'] extends L →+ L' where
  /-- The bracket is preserved. -/
  map_lie' : ∀ x y : L, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆

@[inherit_doc] infixr:25 " →⁅⁆ " => LieRingHom

namespace LieRingHom

variable {L L' L'' : Type*} [LieRing L] [LieRing L'] [LieRing L'']

instance : FunLike (L →⁅⁆ L') L L' where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance : AddMonoidHomClass (L →⁅⁆ L') L L' where
  map_add f := f.map_add'
  map_zero f := f.map_zero'

@[ext]
theorem ext {f g : L →⁅⁆ L'} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

@[simp]
theorem toAddMonoidHom_apply (f : L →⁅⁆ L') (x : L) : f.toAddMonoidHom x = f x := rfl

/-- Lie ring homomorphisms preserve the bracket. -/
@[simp]
theorem map_lie (f : L →⁅⁆ L') (x y : L) : f ⁅x, y⁆ = ⁅f x, f y⁆ := f.map_lie' x y

/-- The identity. -/
protected def id : L →⁅⁆ L := ⟨AddMonoidHom.id L, fun _ _ => rfl⟩

/-- Composition. -/
def comp (g : L' →⁅⁆ L'') (f : L →⁅⁆ L') : L →⁅⁆ L'' :=
  ⟨g.toAddMonoidHom.comp f.toAddMonoidHom, fun x y => by
    change g (f ⁅x, y⁆) = ⁅g (f x), g (f y)⁆
    rw [map_lie, map_lie]⟩

@[simp] theorem id_apply (x : L) : LieRingHom.id x = x := rfl

@[simp] theorem comp_apply (g : L' →⁅⁆ L'') (f : L →⁅⁆ L') (x : L) :
    g.comp f x = g (f x) := rfl

/-- A Lie ring homomorphism is a `ℤ`-Lie algebra homomorphism. -/
def toIntLieHom (f : L →⁅⁆ L') : L →ₗ⁅ℤ⁆ L' where
  toFun := f
  map_add' := map_add f
  map_smul' n x := map_zsmul f n x
  map_lie' := f.map_lie _ _

end LieRingHom

/-- The category of Lie rings. -/
structure LieRingCat : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [str : LieRing carrier]

attribute [instance] LieRingCat.str

namespace LieRingCat

instance : CoeSort LieRingCat (Type u) := ⟨carrier⟩

attribute [coe] carrier

/-- The object of `LieRingCat` attached to a Lie ring. -/
abbrev of (L : Type u) [LieRing L] : LieRingCat := ⟨L⟩

theorem coe_of (L : Type u) [LieRing L] : (of L : Type u) = L := rfl

/-- Morphisms of Lie rings. -/
@[ext]
structure Hom (A B : LieRingCat.{u}) where
  /-- The underlying Lie ring homomorphism. -/
  hom' : A →⁅⁆ B

instance : Category LieRingCat.{u} where
  Hom A B := Hom A B
  id A := ⟨LieRingHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory LieRingCat.{u} (fun A B => A →⁅⁆ B) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- The underlying Lie ring homomorphism of a morphism. -/
abbrev Hom.hom {A B : LieRingCat.{u}} (f : Hom A B) : A →⁅⁆ B :=
  ConcreteCategory.hom (C := LieRingCat) f

/-- A Lie ring homomorphism as a morphism of `LieRingCat`. -/
abbrev ofHom {L L' : Type u} [LieRing L] [LieRing L'] (f : L →⁅⁆ L') : of L ⟶ of L' :=
  ConcreteCategory.ofHom (C := LieRingCat) f

@[simp] lemma hom_id {A : LieRingCat.{u}} : (𝟙 A : A ⟶ A).hom = LieRingHom.id := rfl

@[simp] lemma hom_comp {A B C : LieRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[ext] lemma hom_ext {A B : LieRingCat.{u}} {f g : A ⟶ B} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp] lemma hom_ofHom {L L' : Type u} [LieRing L] [LieRing L'] (f : L →⁅⁆ L') :
    (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom {A B : LieRingCat.{u}} (f : A ⟶ B) : ofHom f.hom = f := rfl

end LieRingCat
