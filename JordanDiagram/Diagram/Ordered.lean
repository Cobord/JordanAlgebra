module

public import JordanDiagram.Diagram.Family
public import Mathlib.Topology.Order.Basic

/-!
# The ordered scalar category

Fix an ordered commutative base ring `k` (for the paper, `Z[1/2]`). The **ordered scalar
category** `OrdScalar k` has as objects the commutative rings `R` with a total, translation
invariant order in which `0 < 1` and products of positives are positive (`IsStrictOrderedRing`),
together with a specified order-preserving `k`-algebra structure `ι_R : k → R`. Its morphisms are
the unital ring homomorphisms commuting with the structure maps, preserving the weak order, and
continuous for the order topologies.

The structure map `ι_R` is object data, not a morphism of `OrdScalar k`: it need not be continuous
(`Diagram/OrderedPowerSeries.lean`: the constant series `k → k⟦t⟧` with `t > 0` infinitesimal).

* `OrdScalar.forget : OrdScalar k ⥤ CommAlgCat k`, the forgetful functor.
* `OrdScalar.exists_pos_lt_of_injective`: an injective morphism carries the positives of the
  source onto a coinitial subset of the positives of the target, so continuous embeddings never
  adjoin infinitesimals; non-injective morphisms such as the constant-term map may specialize
  infinitesimals to zero.
* `orderedAutFunctor F`, `orderedDerFunctor F`: the ordered symmetry functors, `G_F` and `g_F`
  of a diagram restricted to ordered scalars, and `DiagramFamily.orderedAutFunctor`,
  `DiagramFamily.orderedDerFunctor` for families. The shape `I` and its terminal node do not
  change.
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory

namespace JordanDiagram

variable (k : Type u) [CommRing k] [LinearOrder k]

/-- An object of the ordered scalar category: a totally ordered commutative ring with an
order-preserving `k`-algebra structure. -/
structure OrdScalar where
  /-- The underlying ring. -/
  carrier : Type u'
  [commRing : CommRing carrier]
  [linearOrder : LinearOrder carrier]
  [isStrictOrderedRing : IsStrictOrderedRing carrier]
  [algebra : Algebra k carrier]
  monotone_algebraMap : Monotone (algebraMap k carrier)

attribute [instance] OrdScalar.commRing OrdScalar.linearOrder OrdScalar.isStrictOrderedRing
  OrdScalar.algebra

namespace OrdScalar

instance : CoeSort (OrdScalar.{u, u'} k) (Type u') := ⟨carrier⟩

variable {k}

/-- A morphism of ordered scalars: an order-preserving `k`-algebra homomorphism, continuous for
the order topologies. -/
@[ext]
structure Hom (A B : OrdScalar.{u, u'} k) where
  /-- The underlying `k`-algebra homomorphism. -/
  hom : A →ₐ[k] B
  monotone : Monotone hom
  continuous : @Continuous A B (Preorder.topology A) (Preorder.topology B) hom

instance : Category (OrdScalar.{u, u'} k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id k A, monotone_id, @continuous_id A (Preorder.topology A)⟩
  comp {A B C} f g := ⟨g.hom.comp f.hom, g.monotone.comp f.monotone, by
    let _ := Preorder.topology A
    let _ := Preorder.topology B
    let _ := Preorder.topology C
    exact g.continuous.comp f.continuous⟩
  id_comp _ := Hom.ext (AlgHom.ext fun _ => rfl)
  comp_id _ := Hom.ext (AlgHom.ext fun _ => rfl)
  assoc _ _ _ := Hom.ext (AlgHom.ext fun _ => rfl)

theorem id_hom (A : OrdScalar.{u, u'} k) : (𝟙 A : A ⟶ A).hom = AlgHom.id k A := rfl

theorem comp_hom {A B C : OrdScalar.{u, u'} k} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

variable (k) in
/-- The forgetful functor from ordered scalars to commutative `k`-algebras. -/
def forget : OrdScalar.{u, u'} k ⥤ CommAlgCat.{u'} k where
  obj A := CommAlgCat.of k A
  map f := CommAlgCat.ofHom f.hom
  map_id _ := CommAlgCat.ofHom_id
  map_comp f g := CommAlgCat.ofHom_comp f.hom g.hom

theorem forget_map {A B : OrdScalar.{u, u'} k} (f : A ⟶ B) :
    (forget k).map f = CommAlgCat.ofHom f.hom := rfl

end OrdScalar

/-- In a totally ordered ring with `2` invertible, halving keeps a positive element positive and
makes it strictly smaller. -/
theorem mul_invOf_two_mem_Ioo {A : Type*} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]
    [Invertible (2 : A)] {u : A} (hu : 0 < u) : 0 < u * ⅟2 ∧ u * ⅟2 < u := by
  have h1 : (⅟2 : A) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  have hpos : (0 : A) < ⅟2 := by
    by_contra h
    have : (⅟2 : A) + ⅟2 ≤ 0 := add_nonpos (not_lt.1 h) (not_lt.1 h)
    rw [h1] at this
    exact absurd this (not_le.2 one_pos)
  have hlt : (⅟2 : A) < 1 := by rw [← h1]; exact lt_add_of_pos_right _ hpos
  exact ⟨mul_pos hu hpos, mul_lt_of_lt_one_right hu hlt⟩

variable {k} in
/-- **Injective morphisms are coinitial on positives**: for an injective morphism `f : A ⟶ B` of
ordered scalars, the image of `A_{>0}` is coinitial in `B_{>0}`. So continuous order-preserving
embeddings never adjoin elements infinitesimal relative to the source. -/
theorem OrdScalar.exists_pos_lt_of_injective [Invertible (2 : k)] {A B : OrdScalar.{u, u'} k}
    (f : A ⟶ B) (hf : Function.Injective f.hom) {s : B} (hs : 0 < s) :
    ∃ r : A, 0 < r ∧ 0 < f.hom r ∧ f.hom r < s := by
  let _ : TopologicalSpace A := Preorder.topology A
  let _ : TopologicalSpace B := Preorder.topology B
  have _ : OrderTopology A := ⟨rfl⟩
  have _ : OrderTopology B := ⟨rfl⟩
  have _ : Invertible (2 : A) := (Invertible.map (algebraMap k A) 2).copy 2
    (map_ofNat (algebraMap k A) 2).symm
  have hopen : IsOpen (f.hom ⁻¹' Set.Ioo (-s) s) := isOpen_Ioo.preimage f.continuous
  have h0 : (0 : A) ∈ f.hom ⁻¹' Set.Ioo (-s) s := by
    simp only [Set.mem_preimage, map_zero, Set.mem_Ioo, neg_lt_zero]
    exact ⟨hs, hs⟩
  obtain ⟨l, v, ⟨hl, hv⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds h0)
  obtain ⟨hr0, hrv⟩ := mul_invOf_two_mem_Ioo hv
  refine ⟨v * ⅟2, hr0, ?_, (hsub ⟨lt_trans hl hr0, hrv⟩).2⟩
  have hle : f.hom 0 ≤ f.hom (v * ⅟2) := f.monotone hr0.le
  rw [map_zero] at hle
  refine lt_of_le_of_ne hle fun h => hr0.ne' (hf ?_)
  rw [← h, map_zero]

variable {k} [Invertible (2 : k)] {I : Type w} [Category.{w'} I]

/-- `G_F` of a diagram over `k`, restricted to ordered scalars. -/
noncomputable def orderedAutFunctor (F : JordanDiagram.{u, v} k I) :
    OrdScalar.{u, u'} k ⥤ GrpCat.{max u' v w} :=
  OrdScalar.forget k ⋙ autFunctor F

/-- `g_F` of a diagram over `k`, restricted to ordered scalars. -/
noncomputable def orderedDerFunctor (F : JordanDiagram.{u, v} k I) :
    OrdScalar.{u, u'} k ⥤ LieRingCat.{max u' v w} :=
  OrdScalar.forget k ⋙ derFunctor F

theorem orderedAutFunctor_map (F : JordanDiagram.{u, v} k I) {A B : OrdScalar.{u, u'} k}
    (f : A ⟶ B) : (orderedAutFunctor F).map f = GrpCat.ofHom (autMap F f.hom) := rfl

theorem orderedDerFunctor_map (F : JordanDiagram.{u, v} k I) {A B : OrdScalar.{u, u'} k}
    (f : A ⟶ B) : (orderedDerFunctor F).map f = LieRingCat.ofHom (derMap F f.hom) := rfl

namespace DiagramFamily

omit [Invertible (2 : k)]

/-- `G_F` of a family over `CAlg_k`, restricted to ordered scalars. -/
noncomputable def orderedAutFunctor (F : DiagramFamily.{u, u', v} k I) :
    OrdScalar.{u, u'} k ⥤ GrpCat.{max v w} :=
  OrdScalar.forget k ⋙ F.autFunctor

/-- `g_F` of a family over `CAlg_k`, restricted to ordered scalars. -/
noncomputable def orderedDerFunctor (F : DiagramFamily.{u, u', v} k I) :
    OrdScalar.{u, u'} k ⥤ LieRingCat.{max v w} :=
  OrdScalar.forget k ⋙ F.derFunctor

end DiagramFamily

end JordanDiagram
