module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed and open subgroup schemes

A subgroup scheme of a group scheme over a base scheme `S` is a subscheme whose inclusion is
compatible with the group structure. Its inclusion may be a closed or an open immersion. A
closed or open subscheme of a group scheme is a subgroup scheme precisely when the identity,
the multiplication on its self-product over the base, and the inverse all factor through the
subscheme.

## Main definitions

* `AlgebraicGeometry.ClosedSubgroupScheme` bundles a group scheme with a closed-immersion
  homomorphism into a given group scheme.
* `AlgebraicGeometry.OpenSubgroupScheme` is the corresponding notion for an open immersion.

## Main results

* `AlgebraicGeometry.isClosedSubgroupScheme_iff_factor` is the factorization criterion in the
  closed case.
* `AlgebraicGeometry.isOpenSubgroupScheme_iff_factor` is the factorization criterion in the
  open case.

## Implementation notes

A group scheme over `S` is a group object in schemes over `S`, and the fibre product over the
base is the tensor product of that cartesian monoidal category. A morphism in `Grp (Over S)`
records compatibility with multiplication, identity and inverse; its underlying immersion
exhibits the required subscheme, so the multiplication of the ambient scheme restricts to the
subgroup scheme. A subgroup scheme is exhibited by a group object together with an isomorphism
of its underlying scheme over the base onto the given subscheme, commuting with the inclusion
into the ambient group scheme.

## References

* [Stacks Project, Tag 047D](https://stacks.math.columbia.edu/tag/047D)
* [Stacks Project, Tag 0G8L](https://stacks.math.columbia.edu/tag/0G8L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A closed subgroup scheme of `G` over `S`. -/
@[stacks 047D "part (1)"]
structure ClosedSubgroupScheme {S : Scheme.{u}} (G : Grp (Over S)) where
  /-- The subgroup scheme as a group object over the base. -/
  carrier : Grp (Over S)
  /-- The inclusion, compatible with the group-scheme structure. -/
  ι : carrier ⟶ G
  /-- The underlying inclusion is a closed immersion of schemes. -/
  isClosedImmersion : IsClosedImmersion ι.hom.hom.left

/-- An open subgroup scheme of `G` over `S`. -/
@[stacks 047D "part (2)"]
structure OpenSubgroupScheme {S : Scheme.{u}} (G : Grp (Over S)) where
  /-- The subgroup scheme as a group object over the base. -/
  carrier : Grp (Over S)
  /-- The inclusion, compatible with the group-scheme structure. -/
  ι : carrier ⟶ G
  /-- The underlying inclusion is an open immersion of schemes. -/
  isOpenImmersion : IsOpenImmersion ι.hom.hom.left

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj CategoryTheory.GrpObj

/-- A monomorphism into a group object carries a group-object structure as soon as the identity,
the multiplication and the inverse factor through it. -/
@[instance_reducible]
private def groupObjectOfFactors {C : Type u} [Category C] [CartesianMonoidalCategory C]
    (G : Grp C) (H : C) (j : H ⟶ G.X)
    [Mono j] (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (i : H ⟶ H)
    (he : e ≫ j = η[G.X])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G.X])
    (hi : i ≫ j = j ≫ ι[G.X]) : GrpObj H := by
  letI : MonObj H :=
    { one := e
      mul := m
      one_mul := by
        apply (cancel_mono j).1
        calc
          (e ▷ H ≫ m) ≫ j = (e ▷ H) ≫ (j ⊗ₘ j) ≫ μ[G.X] := by rw [Category.assoc, hm]
          _ = (η[G.X] ⊗ₘ j) ≫ μ[G.X] := by rw [whiskerRight_comp_tensorHom_assoc, he]
          _ = (λ_ H).hom ≫ j := MonObj.one_mul_hom j
      mul_one := by
        apply (cancel_mono j).1
        calc
          (H ◁ e ≫ m) ≫ j = (H ◁ e) ≫ (j ⊗ₘ j) ≫ μ[G.X] := by rw [Category.assoc, hm]
          _ = (j ⊗ₘ η[G.X]) ≫ μ[G.X] := by rw [whiskerLeft_comp_tensorHom_assoc, he]
          _ = (ρ_ H).hom ≫ j := MonObj.mul_one_hom j
      mul_assoc := by
        apply (cancel_mono j).1
        calc
          (m ▷ H ≫ m) ≫ j = (m ▷ H) ≫ (j ⊗ₘ j) ≫ μ[G.X] := by rw [Category.assoc, hm]
          _ = (m ≫ j ⊗ₘ j) ≫ μ[G.X] := by rw [whiskerRight_comp_tensorHom_assoc]
          _ = ((j ⊗ₘ j) ≫ μ[G.X] ⊗ₘ j) ≫ μ[G.X] := by rw [hm]
          _ = ((j ⊗ₘ j) ⊗ₘ j) ≫ (μ[G.X] ▷ G.X) ≫ μ[G.X] := by
            rw [← tensorHom_comp_whiskerRight_assoc]
          _ = ((j ⊗ₘ j) ⊗ₘ j) ≫ ((α_ G.X G.X G.X).hom ≫ (G.X ◁ μ[G.X]) ≫ μ[G.X]) := by
            rw [MonObj.mul_assoc]
          _ = ((α_ H H H).hom ≫ (j ⊗ₘ (j ⊗ₘ j))) ≫ (G.X ◁ μ[G.X]) ≫ μ[G.X] := by
            simp [Category.assoc]
          _ = ((α_ H H H).hom ≫ (j ⊗ₘ ((j ⊗ₘ j) ≫ μ[G.X]))) ≫ μ[G.X] := by
            simpa [Category.assoc] using congrArg (fun f => (α_ H H H).hom ≫ f ≫ μ[G.X])
              (tensorHom_comp_whiskerLeft j (j ⊗ₘ j) μ[G.X])
          _ = ((α_ H H H).hom ≫ (j ⊗ₘ (m ≫ j))) ≫ μ[G.X] := by rw [← hm]
          _ = ((α_ H H H).hom ≫ (H ◁ m) ≫ (j ⊗ₘ j)) ≫ μ[G.X] := by
            simpa [Category.assoc] using congrArg (fun f => (α_ H H H).hom ≫ f ≫ μ[G.X])
              (whiskerLeft_comp_tensorHom j m j).symm
          _ = ((α_ H H H).hom ≫ (H ◁ m) ≫ m) ≫ j := by
            simpa [Category.assoc] using
              congrArg (fun f => ((α_ H H H).hom ≫ (H ◁ m)) ≫ f) hm.symm }
  letI : IsMonHom j := ⟨he, hm⟩
  letI : GrpObj H :=
    { toMonObj := inferInstance
      inv := i
      left_inv := by
        apply (cancel_mono j).1
        calc
          (lift i (𝟙 H) ≫ m) ≫ j = lift i (𝟙 H) ≫ (j ⊗ₘ j) ≫ μ[G.X] := by
            rw [Category.assoc, hm]
          _ = lift (i ≫ j) ((𝟙 H) ≫ j) ≫ μ[G.X] := by
            simp
          _ = j ≫ (lift ι[G.X] (𝟙 G.X) ≫ μ[G.X]) := by
            simp only [hi, Category.id_comp]
            simp
          _ = (toUnit H ≫ e) ≫ j := by rw [GrpObj.left_inv]; simp [he]
      right_inv := by
        apply (cancel_mono j).1
        calc
          (lift (𝟙 H) i ≫ m) ≫ j = lift (𝟙 H) i ≫ (j ⊗ₘ j) ≫ μ[G.X] := by
            rw [Category.assoc, hm]
          _ = lift ((𝟙 H) ≫ j) (i ≫ j) ≫ μ[G.X] := by
            simp
          _ = j ≫ (lift (𝟙 G.X) ι[G.X] ≫ μ[G.X]) := by
            simp only [hi, Category.id_comp]
            simp
          _ = (toUnit H ≫ e) ≫ j := by rw [GrpObj.right_inv]; simp [he] }
  exact inferInstance

/-- A monomorphism `j` into a group scheme is the inclusion of a subgroup scheme with property `P`
of the underlying morphism iff the identity, multiplication and inverse factor through it. -/
private theorem exists_subgroup_iff_factor {S : Scheme.{u}} (G : Grp (Over S)) {H : Over S}
    (j : H ⟶ G.X) [Mono j] (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Prop) (hP : P j.left) :
    (∃ (K : Grp (Over S)) (f : K ⟶ G), P f.hom.hom.left ∧
      ∃ e : H ≅ K.X, j = e.hom ≫ f.hom.hom) ↔
      ((∃ e : 𝟙_ (Over S) ⟶ H, e ≫ j = η[G.X]) ∧
       (∃ m : H ⊗ H ⟶ H, m ≫ j = (j ⊗ₘ j) ≫ μ[G.X]) ∧
       (∃ i : H ⟶ H, i ≫ j = j ≫ ι[G.X])) := by
  constructor
  · rintro ⟨K, f, -, e, hj⟩
    refine ⟨⟨η[K.X] ≫ e.inv, ?_⟩, ⟨(e.hom ⊗ₘ e.hom) ≫ μ[K.X] ≫ e.inv, ?_⟩,
      ⟨e.hom ≫ ι[K.X] ≫ e.inv, ?_⟩⟩ <;> simp [Category.assoc, hj]
  · rintro ⟨⟨e, he⟩, ⟨m, hm⟩, ⟨i, hi⟩⟩
    let : GrpObj H := groupObjectOfFactors G H j e m i he hm hi
    let : IsMonHom j := ⟨he, hm⟩
    exact ⟨Grp.mk H, Grp.homMk j, hP, Iso.refl H, rfl⟩

/-- The factorization criterion for a closed subscheme to be a subgroup scheme. -/
@[stacks 0G8L "part (1)"]
theorem isClosedSubgroupScheme_iff_factor {S : Scheme.{u}}
    (G : Grp (Over S)) {H : Over S} (j : H ⟶ G.X)
    [AlgebraicGeometry.IsClosedImmersion j.left] :
    (∃ K : ClosedSubgroupScheme G,
      ∃ e : H ≅ K.carrier.X, j = e.hom ≫ K.ι.hom.hom) ↔
      ((∃ e : 𝟙_ (Over S) ⟶ H, e ≫ j = η[G.X]) ∧
       (∃ m : H ⊗ H ⟶ H, m ≫ j = (j ⊗ₘ j) ≫ μ[G.X]) ∧
       (∃ i : H ⟶ H, i ≫ j = j ≫ ι[G.X])) := by
  have : Mono j := Over.mono_of_mono_left j
  rw [← exists_subgroup_iff_factor G j @IsClosedImmersion inferInstance]
  exact ⟨fun ⟨K, e, hj⟩ => ⟨K.carrier, K.ι, K.isClosedImmersion, e, hj⟩,
    fun ⟨K, f, hf, e, hj⟩ => ⟨⟨K, f, hf⟩, e, hj⟩⟩

/-- The factorization criterion for an open subscheme to be a subgroup scheme. -/
@[stacks 0G8L "part (2)"]
theorem isOpenSubgroupScheme_iff_factor {S : Scheme.{u}}
    (G : Grp (Over S)) {H : Over S} (j : H ⟶ G.X)
    [AlgebraicGeometry.IsOpenImmersion j.left] :
    (∃ K : OpenSubgroupScheme G,
      ∃ e : H ≅ K.carrier.X, j = e.hom ≫ K.ι.hom.hom) ↔
      ((∃ e : 𝟙_ (Over S) ⟶ H, e ≫ j = η[G.X]) ∧
       (∃ m : H ⊗ H ⟶ H, m ≫ j = (j ⊗ₘ j) ≫ μ[G.X]) ∧
       (∃ i : H ⟶ H, i ≫ j = j ≫ ι[G.X])) := by
  have : Mono j := Over.mono_of_mono_left j
  rw [← exists_subgroup_iff_factor G j @IsOpenImmersion inferInstance]
  exact ⟨fun ⟨K, e, hj⟩ => ⟨K.carrier, K.ι, K.isOpenImmersion, e, hj⟩,
    fun ⟨K, f, hf, e, hj⟩ => ⟨⟨K, f, hf⟩, e, hj⟩⟩

end AlgebraicGeometry
