import JordanDiagram.Diagram.BaseChange
import JordanDiagram.Algebra.Functor
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The diagram group functor `G_F : CAlg_R → Grp` (Proposition 3.3)

For a diagram `F : I → Jord_R`, with `2` invertible in `R`, the groups `G_F(S)` of the scalar
extensions `S ⊗[R] F` form a functor on commutative `R`-algebras:

* `autMap F φ : G_F(S) →* G_F(T)` for `φ : S →ₐ[R] T`, transporting each component along `φ`
  (`JordanAlgebra.BaseChange.mapAut`);
* `autMap_id`, `autMap_comp`: the functor laws;
* `autMap_comp_autBaseChange`: compatibility with `G_F(R) → G_F(S)`;
* `autFunctor F : CommAlgCat R ⥤ GrpCat`, the functor `G_F` itself.

For `R = Z[1/2]` the category `CommAlgCat R` is `CAlg_{Z[1/2]}` of the paper (Lemma 2.2), and
`autFunctor F` is the group-valued functor of Proposition 3.3 for the family `F_S = S ⊗ F`
(Lemma 2.11).
-/

universe u u' v w w'

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange

namespace JordanDiagram

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} R I)
variable {S T U : Type u'} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  [CommRing U] [Algebra R U]

/-- **Proposition 3.3**: `G_F(φ) : G_F(S) →* G_F(T)` for `φ : S →ₐ[R] T`. -/
noncomputable def autMap (φ : S →ₐ[R] T) : (F.baseChange S).autGroup →* (F.baseChange T).autGroup where
  toFun g := ⟨fun i => mapAut φ (g.1 i), fun α x =>
    mapLin_baseChangeHom_comm φ (F.map α) _ _ (fun y => autGroup_naturality g α y) x⟩
  map_one' := Subtype.ext (funext fun _ => map_one (mapAut φ))
  map_mul' g h := Subtype.ext (funext fun i => map_mul (mapAut φ) (g.1 i) (h.1 i))

theorem autMap_apply (φ : S →ₐ[R] T) (g : (F.baseChange S).autGroup) (i : I) :
    (autMap F φ g).1 i = mapAut φ (g.1 i) := rfl

/-- `G_F(id) = id`. -/
theorem autMap_id : autMap F (AlgHom.id R S) = MonoidHom.id _ :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i => mapAut_id_alg (g.1 i))

/-- `G_F(χ ∘ φ) = G_F(χ) ∘ G_F(φ)`. -/
theorem autMap_comp (φ : S →ₐ[R] T) (χ : T →ₐ[R] U) :
    autMap F (χ.comp φ) = (autMap F χ).comp (autMap F φ) :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i => mapAut_comp_alg φ χ (g.1 i))

/-- `G_F(φ) ∘ (G_F(R) → G_F(S)) = (G_F(R) → G_F(T))`. -/
theorem autMap_comp_autBaseChange (φ : S →ₐ[R] T) :
    (autMap F φ).comp (autBaseChange S F) = autBaseChange T F :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i => mapAut_baseChangeAut φ (g.1 i))

/-- **Proposition 3.3**: the diagram automorphism group functor
`G_F : CAlg_R → Grp`, `S ↦ Aut(S ⊗[R] F)`. -/
noncomputable def autFunctor : CommAlgCat.{u'} R ⥤ GrpCat.{max u' v w} where
  obj S := GrpCat.of (F.baseChange S).autGroup
  map φ := GrpCat.ofHom (autMap F φ.hom)
  map_id S := by
    apply GrpCat.hom_ext
    rw [GrpCat.hom_ofHom, CommAlgCat.hom_id, autMap_id]
    rfl
  map_comp φ χ := by
    apply GrpCat.hom_ext
    rw [GrpCat.hom_ofHom, CommAlgCat.hom_comp, autMap_comp]
    rfl

@[simp]
theorem autFunctor_obj (S : CommAlgCat.{u'} R) :
    (autFunctor F).obj S = GrpCat.of (F.baseChange S).autGroup := rfl

theorem autFunctor_map {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    (autFunctor F).map φ = GrpCat.ofHom (autMap F φ.hom) := rfl

end JordanDiagram
