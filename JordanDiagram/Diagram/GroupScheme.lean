module

public import JordanDiagram.Diagram.Representability
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecRingHomEquiv
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# The diagram group scheme

For a diagram `F` over `k` with finite free nodes, the group functor `T ↦ G_F(Γ(T))` on schemes over
`Spec k` is represented by `Spec B`, for the representing algebra `B` of
`Diagram/Representability.lean`; so `Spec B` is a group object over `Spec k` whose group of
`T`-points is `G_F(Γ(T))`. Morphisms `T ⟶ Spec B` are ring maps `B → Γ(T)` through
`AlgebraicGeometry.specRingHomEquiv` (from the Stacks Project in Lean, vendored).

* `globalSections k`: `T ↦ Γ(T)` as a functor from schemes over `Spec k` to commutative
  `k`-algebras, with `k` acting through the structure morphism.
* `homEquivAlg`: morphisms `T ⟶ Spec A` over `Spec k` are `k`-algebra maps `A → Γ(T)`.
* `pointsFunctor F`: the group functor `T ↦ G_F(Γ(T))`; `schemeOf F b = Spec B` represents it
  (`representableBy`), so it is a group object over `Spec k` (`grpObj`) with
  `pointsIso : yonedaGrpObj (schemeOf F b) ≅ pointsFunctor F` as presheaves of groups.
* `glPoints F`, `schemeGL F b`, `grpObjGL`, `pointsIsoGL`: the same for `∏ᵢ GL(F(i))`, represented by
  `Spec k[∏ GL]`.
* `isMonHom_of_comp_mul`: a morphism of group objects that is multiplicative on points is a
  homomorphism.
* `closedSubgroup`: `Spec B ⟶ Spec k[∏ GL]` is a homomorphism and a closed immersion, taking a
  diagram automorphism to its components (`representableByGL_inclusion`): **the diagram group
  scheme is a closed subgroup scheme of `∏ᵢ GL(F(i))`** (`ClosedSubgroupScheme`, vendored from the
  Stacks Project in Lean).
* `groupScheme`: the basis-free statement.

Here everything lives in one universe (ring, shape and nodes), as schemes do.
-/

@[expose] public section

universe u w'

open CategoryTheory Opposite AlgebraicGeometry JordanDiagram.Representability TensorProduct
  JordanAlgebra JordanAlgebra.BaseChange

namespace JordanDiagram

variable (k : Type u) [CommRing k]

/-- The base scheme `Spec k`. -/
noncomputable abbrev baseScheme : Scheme.{u} := Spec (CommRingCat.of k)

variable {k}

/-- The structure map `k → Γ(T)` of a scheme over `Spec k`. -/
noncomputable def structHom (T : Over (baseScheme k)) : k →+* Scheme.Γ.obj (op T.left) :=
  specRingHomEquiv k T.left T.hom

/-- Morphisms into `Spec S` followed by `Spec φ` correspond to ring maps composed with `φ`. -/
theorem specRingHomEquiv_comp_specMap {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of S)) (φ : R →+* S) :
    specRingHomEquiv R X (g ≫ Spec.map (CommRingCat.ofHom φ)) =
      (specRingHomEquiv S X g).comp φ := by
  have h := specRingHomEquiv_comp S g (𝟙 _)
  rw [Category.comp_id, specRingHomEquiv_id] at h
  rw [specRingHomEquiv_comp, specRingHomEquiv_specMap, h]
  exact (RingHom.comp_assoc _ _ _).symm

/-- The ring map `Γ(T') → Γ(T)` of a morphism `f : T ⟶ T'` over `Spec k` is `k`-linear. -/
theorem structHom_comp {T T' : Over (baseScheme k)} (f : T ⟶ T') :
    (Scheme.Γ.map f.left.op).hom.comp (structHom T') = structHom T := by
  rw [structHom, structHom, ← specRingHomEquiv_comp, Over.w]

/-- The global sections `Γ(T)` of a scheme over `Spec k`, as a `k`-algebra through the structure
morphism. -/
noncomputable def sectionsAlg (T : Over (baseScheme k)) : CommAlgCat.{u} k where
  carrier := Scheme.Γ.obj (op T.left)
  algebra := (structHom T).toAlgebra

theorem algebraMap_sectionsAlg (T : Over (baseScheme k)) (r : k) :
    algebraMap k (sectionsAlg T) r = structHom T r := rfl

/-- The `k`-algebra map `Γ(T') → Γ(T)` of a morphism `T ⟶ T'` over `Spec k`. -/
noncomputable def sectionsMap {T T' : Over (baseScheme k)} (f : T ⟶ T') :
    sectionsAlg T' →ₐ[k] sectionsAlg T where
  toRingHom := (Scheme.Γ.map f.left.op).hom
  commutes' r := RingHom.congr_fun (structHom_comp f) r

theorem sectionsMap_apply {T T' : Over (baseScheme k)} (f : T ⟶ T') (x : sectionsAlg T') :
    sectionsMap f x = (Scheme.Γ.map f.left.op).hom x := rfl

variable (k) in
/-- Global sections, as commutative `k`-algebras through the structure morphism. -/
noncomputable def globalSections : (Over (baseScheme k))ᵒᵖ ⥤ CommAlgCat.{u} k where
  obj T := sectionsAlg T.unop
  map f := ConcreteCategory.ofHom (C := CommAlgCat k) (sectionsMap f.unop)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun x => by
    change (Scheme.Γ.map (𝟙 T.unop.left).op).hom x = x
    simp only [op_id, CategoryTheory.Functor.map_id]
    rfl)
  map_comp f g := CommAlgCat.hom_ext (AlgHom.ext fun x => by
    change (Scheme.Γ.map (g.unop.left ≫ f.unop.left).op).hom x =
      (Scheme.Γ.map g.unop.left.op).hom ((Scheme.Γ.map f.unop.left.op).hom x)
    rw [op_comp, CategoryTheory.Functor.map_comp]
    rfl)

/-! ### Affine schemes over `Spec k` -/

section Affine

variable (A : Type u) [CommRing A] [Algebra k A]

/-- `Spec A` as a scheme over `Spec k`. -/
noncomputable abbrev specOver : Over (baseScheme k) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- Morphisms `T ⟶ Spec A` over `Spec k` are `k`-algebra maps `A → Γ(T)`. -/
noncomputable def homEquivAlg (T : Over (baseScheme k)) :
    (T ⟶ specOver A) ≃ (A →ₐ[k] sectionsAlg T) where
  toFun g :=
    { toRingHom := specRingHomEquiv A T.left g.left
      commutes' r := by
        rw [algebraMap_sectionsAlg, structHom, ← Over.w g]
        exact (RingHom.congr_fun (specRingHomEquiv_comp_specMap g.left (algebraMap k A)) r).symm }
  invFun φ := Over.homMk ((specRingHomEquiv A T.left).symm φ.toRingHom) (by
    apply (specRingHomEquiv k T.left).injective
    refine (specRingHomEquiv_comp_specMap ((specRingHomEquiv A T.left).symm φ.toRingHom)
      (algebraMap k A)).trans (RingHom.ext fun r => ?_)
    exact (RingHom.congr_fun (Equiv.apply_symm_apply (specRingHomEquiv A T.left)
      φ.toRingHom) (algebraMap k A r)).trans (φ.commutes r))
  left_inv g := Over.OverMorphism.ext (Equiv.symm_apply_apply _ _)
  right_inv φ := AlgHom.ext fun x =>
    RingHom.congr_fun (Equiv.apply_symm_apply (specRingHomEquiv A T.left) φ.toRingHom) x

theorem homEquivAlg_comp {T T' : Over (baseScheme k)} (f : T ⟶ T') (g : T' ⟶ specOver A) :
    homEquivAlg A T (f ≫ g) = (sectionsMap f).comp (homEquivAlg A T' g) :=
  AlgHom.ext fun x => RingHom.congr_fun (specRingHomEquiv_comp A f.left g.left) x

variable {A} {A' : Type u} [CommRing A'] [Algebra k A']

/-- The morphism `Spec A ⟶ Spec A'` over `Spec k` of a `k`-algebra map `A' → A`. -/
noncomputable def specOverMap (φ : A' →ₐ[k] A) : specOver (k := k) A ⟶ specOver A' :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A')) = Spec.map (CommRingCat.ofHom (algebraMap k A))
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r => φ.commutes r))

/-- Composing with `Spec φ` is composing the algebra map with `φ`. -/
theorem homEquivAlg_specOverMap (φ : A' →ₐ[k] A) {T : Over (baseScheme k)} (g : T ⟶ specOver A) :
    homEquivAlg A' T (g ≫ specOverMap φ) = (homEquivAlg A T g).comp φ :=
  AlgHom.ext fun x =>
    RingHom.congr_fun (specRingHomEquiv_comp_specMap g.left φ.toRingHom) x

end Affine

/-! ### A group-object homomorphism, detected on points -/

open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- A morphism between group objects that is multiplicative on points is a homomorphism of group
objects. -/
theorem isMonHom_of_comp_mul {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N : C}
    [GrpObj M] [GrpObj N] (j : M ⟶ N)
    (h : ∀ (X : C) (f g : X ⟶ M), (f * g) ≫ j = (f ≫ j) * (g ≫ j)) : IsMonHom j where
  one_hom := by
    have h1 := h (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ M) ≫ j = 1 := by
      have := congrArg (fun z => z * ((1 : 𝟙_ C ⟶ M) ≫ j)⁻¹) h1
      simpa using this.symm
    simpa [Hom.one_def] using h2
  mul_hom := by
    have := h (M ⊗ M) (fst M M) (snd M M)
    simpa [Hom.mul_def] using this

/-! ### The group functor and its representing scheme -/

variable [Invertible (2 : k)] {I : Type u} [Category.{w'} I] (F : JordanDiagram.{u, u} k I)

/-- The group functor `T ↦ G_F(Γ(T))` on schemes over `Spec k`. -/
noncomputable def pointsFunctor : (Over (baseScheme k))ᵒᵖ ⥤ GrpCat.{u} :=
  globalSections k ⋙ autFunctor F

section Bases

variable {ι : I → Type u} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
  (b : ∀ i, Module.Basis (ι i) k (F.obj i))

/-- `Spec B` as a scheme over `Spec k`, for the representing algebra `B`. -/
noncomputable abbrev schemeOf : Over (baseScheme k) := specOver (k := k) (Rep F b)

/-- **`Spec B` represents `T ↦ G_F(Γ(T))`.** -/
noncomputable def representableBy :
    (pointsFunctor F ⋙ forget GrpCat).RepresentableBy (schemeOf F b) where
  homEquiv {T} := (homEquivAlg (Rep F b) T).trans (algHomEquiv F b)
  homEquiv_comp {T T'} f g := by
    change algHomEquiv F b (homEquivAlg (Rep F b) T (f ≫ g)) =
      autMap F (sectionsMap f) (algHomEquiv F b (homEquivAlg (Rep F b) T' g))
    rw [homEquivAlg_comp, algHomEquiv_comp]

/-- **The diagram group scheme**: `Spec B` is a group object over `Spec k`. -/
noncomputable instance grpObj : GrpObj (schemeOf F b) :=
  GrpObj.ofRepresentableBy _ _ (representableBy F b)

/-- **The `T`-points of the diagram group scheme are `G_F(Γ(T))`, as groups**, naturally in `T`. -/
noncomputable def pointsIso : yonedaGrpObj (schemeOf F b) ≅ pointsFunctor F :=
  yonedaGrpObjIsoOfRepresentableBy _ _ (representableBy F b)

open MonObj in
theorem representableBy_mul {T : Over (baseScheme k)} (f g : T ⟶ schemeOf F b) :
    (representableBy F b).homEquiv (f * g) =
      (representableBy F b).homEquiv f * (representableBy F b).homEquiv g :=
  ((pointsIso F b).hom.app (op T)).hom.map_mul f g

end Bases

/-! ### The general linear group scheme `∏ᵢ GL(F(i))` -/

/-- The group `∏ᵢ GL(S ⊗ F(i))`. -/
abbrev glGroup (S : Type u) [CommRing S] [Algebra k S] : Type u :=
  ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i

/-- Transport of linear automorphisms along `χ : S →ₐ[k] T`. -/
noncomputable def mapGL {S T : Type u} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
    (χ : S →ₐ[k] T) : glGroup F S →* glGroup F T where
  toFun g i := LinearEquiv.ofLinearMap (mapLin χ (g i).toLinearMap) (mapLin χ (g i).symm.toLinearMap)
    (by rw [← mapLin_comp, LinearEquiv.comp_symm, mapLin_id])
    (by rw [← mapLin_comp, LinearEquiv.symm_comp, mapLin_id])
  map_one' := funext fun i => LinearEquiv.toLinearMap_injective (mapLin_id χ)
  map_mul' g h := funext fun i => LinearEquiv.toLinearMap_injective (mapLin_comp χ _ _)

/-- `S ↦ ∏ᵢ GL(S ⊗ F(i))` as a functor on commutative `k`-algebras. -/
noncomputable def glFunctor : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj S := GrpCat.of (glGroup F S)
  map χ := GrpCat.ofHom (mapGL F χ.hom)
  map_id _ := GrpCat.hom_ext (MonoidHom.ext fun _ => funext fun _ =>
    LinearEquiv.toLinearMap_injective (mapLin_id_alg _))
  map_comp χ ψ := GrpCat.hom_ext (MonoidHom.ext fun _ => funext fun _ =>
    LinearEquiv.toLinearMap_injective (mapLin_comp_alg χ.hom ψ.hom _))

/-- The group functor `T ↦ ∏ᵢ GL(Γ(T) ⊗ F(i))` on schemes over `Spec k`. -/
noncomputable def glPoints : (Over (baseScheme k))ᵒᵖ ⥤ GrpCat.{u} :=
  globalSections k ⋙ glFunctor F

/-- The components of a diagram automorphism, a group homomorphism `G_F(S) →* ∏ᵢ GL(S ⊗ F(i))`. -/
def components (S : Type u) [CommRing S] [Algebra k S] :
    (F.baseChange S).autGroup →* glGroup F S where
  toFun g i := (g.1 i : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i)
  map_one' := rfl
  map_mul' _ _ := rfl

section BasesGL

variable {ι : I → Type u} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
  (b : ∀ i, Module.Basis (ι i) k (F.obj i))

omit [Invertible (2 : k)] in
theorem glEquiv_comp {S T : Type u} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
    (χ : S →ₐ[k] T) (f : RepGL k ι →ₐ[k] S) :
    glEquiv F b (χ.comp f) = mapGL F χ (glEquiv F b f) :=
  funext fun i => LinearEquiv.ext fun x => by
    change _ = mapLin χ (endo F b S i (mat (fun y => f (Ideal.Quotient.mk _ (gen k ι y))) true i)) x
    rw [mapLin_endo]
    rfl

set_option linter.unusedVariables false in
/-- `Spec k[∏ GL]` as a scheme over `Spec k`, for the nodes of `F` with the bases `b` (on which the
underlying scheme does not depend; the group structure `grpObjGL` is that of `∏ᵢ GL(F(i))`). -/
noncomputable abbrev schemeGL (F' : JordanDiagram.{u, u} k I)
    (b' : ∀ i, Module.Basis (ι i) k (F'.obj i)) : Over (baseScheme k) :=
  specOver (k := k) (RepGL k ι)

/-- **`Spec k[∏ GL]` represents `T ↦ ∏ᵢ GL(Γ(T) ⊗ F(i))`.** -/
noncomputable def representableByGL :
    (glPoints F ⋙ forget GrpCat).RepresentableBy (schemeGL F b) where
  homEquiv {T} := (homEquivAlg (RepGL k ι) T).trans (glEquiv F b)
  homEquiv_comp {T T'} f g := by
    change glEquiv F b (homEquivAlg (RepGL k ι) T (f ≫ g)) =
      mapGL F (sectionsMap f) (glEquiv F b (homEquivAlg (RepGL k ι) T' g))
    rw [homEquivAlg_comp, glEquiv_comp]

/-- The general linear group scheme `∏ᵢ GL(F(i))` over `Spec k`. -/
noncomputable instance grpObjGL : GrpObj (schemeGL F b) :=
  GrpObj.ofRepresentableBy _ _ (representableByGL F b)

/-- The `T`-points of `∏ᵢ GL(F(i))` are `∏ᵢ GL(Γ(T) ⊗ F(i))`, as groups. -/
noncomputable def pointsIsoGL : yonedaGrpObj (schemeGL F b) ≅ glPoints F :=
  yonedaGrpObjIsoOfRepresentableBy _ _ (representableByGL F b)

omit [Invertible (2 : k)] in
open MonObj in
theorem representableByGL_mul {T : Over (baseScheme k)} (f g : T ⟶ schemeGL F b) :
    (representableByGL F b).homEquiv (f * g) =
      (representableByGL F b).homEquiv f * (representableByGL F b).homEquiv g :=
  ((pointsIsoGL F b).hom.app (op T)).hom.map_mul f g

/-! ### The diagram group scheme is a closed subgroup scheme of `∏ᵢ GL(F(i))` -/

/-- The inclusion `Spec B ⟶ Spec k[∏ GL]`, the spectrum of the quotient map. -/
noncomputable abbrev inclusion : schemeOf F b ⟶ schemeGL F b :=
  specOverMap (toRep F b)

/-- On points, the inclusion takes a diagram automorphism to its components. -/
theorem representableByGL_inclusion {T : Over (baseScheme k)} (x : T ⟶ schemeOf F b) :
    (representableByGL F b).homEquiv (x ≫ inclusion F b) =
      components F (sectionsAlg T) ((representableBy F b).homEquiv x) := by
  change glEquiv F b (homEquivAlg (RepGL k ι) T (x ≫ specOverMap (toRep F b))) = _
  rw [homEquivAlg_specOverMap]
  exact funext fun i => glEquiv_comp_toRep F b _ i

open MonObj in
/-- The inclusion is a homomorphism of group schemes. -/
instance isMonHom_inclusion : IsMonHom (inclusion F b) :=
  isMonHom_of_comp_mul _ fun _ f g => (representableByGL F b).homEquiv.injective (by
    rw [representableByGL_mul, representableByGL_inclusion, representableByGL_inclusion,
      representableByGL_inclusion, representableBy_mul]
    exact map_mul (components F _) _ _)

/-- **The diagram group scheme is a closed subgroup scheme of `∏ᵢ GL(F(i))`.** -/
noncomputable def closedSubgroup : ClosedSubgroupScheme (Grp.mk (schemeGL F b)) where
  carrier := Grp.mk (schemeOf F b)
  ι := Grp.homMk (inclusion F b)
  isClosedImmersion :=
    IsClosedImmersion.spec_of_surjective _ (toRep_surjective F b)

end BasesGL

open MonObj in
/-- **The diagram group scheme** (basis-free form). For a diagram with finite free nodes there are
`k`-algebras `B` and `A` such that `Spec B` and `Spec A` are group schemes over `Spec k` whose
groups of `T`-points are `G_F(Γ(T))` and `∏ᵢ GL(Γ(T) ⊗ F(i))`, naturally in `T`, and a
homomorphism of group schemes `Spec B ⟶ Spec A` that is a closed immersion and takes a diagram
automorphism to its components: `Spec B` is a closed subgroup scheme of `∏ᵢ GL(F(i))`. `B` is of
finite type when the shape has finitely many objects. -/
theorem groupScheme [∀ i, Module.Free k (F.obj i)] [∀ i, Module.Finite k (F.obj i)] :
    ∃ (B A : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : CommRing A) (_ : Algebra k A)
      (_ : GrpObj (specOver (k := k) B)) (_ : GrpObj (specOver (k := k) A))
      (eB : yonedaGrpObj (specOver (k := k) B) ≅ pointsFunctor F)
      (eA : yonedaGrpObj (specOver (k := k) A) ≅ glPoints F)
      (j : specOver (k := k) B ⟶ specOver A), IsMonHom j ∧ IsClosedImmersion j.left ∧
      (∀ (T : Over (baseScheme k)) (x : T ⟶ specOver (k := k) B),
        (eA.hom.app (op T)).hom (x ≫ j) = components F (sectionsAlg T) ((eB.hom.app (op T)).hom x)) ∧
      (Finite I → Algebra.FiniteType k B) := by
  classical
  let b := fun i => Module.Free.chooseBasis k (F.obj i)
  exact ⟨Rep F b, RepGL k _, inferInstance, inferInstance, inferInstance, inferInstance,
    grpObj F b, grpObjGL F b, pointsIso F b, pointsIsoGL F b, inclusion F b,
    isMonHom_inclusion F b, IsClosedImmersion.spec_of_surjective _ (toRep_surjective F b),
    fun T x => representableByGL_inclusion F b x, fun _ => finiteType F b⟩

end JordanDiagram
