module

public import JordanDiagram.Diagram.Functor
public import JordanDiagram.Diagram.Iso
public import JordanDiagram.MathlibMissing.SemilinearBaseChange

/-!
# Families of diagrams over varying base rings

A **terminally pointed Jordan-diagram family** of shape `I` over the commutative `R`-algebras
(`DiagramFamily`) assigns a diagram `F_S : I → Jord_S` to every `S`, and to every `φ : S → T` a
natural isomorphism `β_φ : F_S ⊗_S T ≅ F_T` satisfying the identity and composition coherences.
For `R = Z[1/2]`, `CAlg_R` is the category of commutative rings in which `2` is invertible, since
the structure map from `Z[1/2]` is then unique.

Here `β_φ` is recorded by its restriction `F_S(i) → F_T(i)`, `x ↦ β_φ(x ⊗ 1)`: a `φ`-semilinear,
multiplicative map, natural in `i`, which is a base change (stated by its universal property
`IsSemilinearBaseChange`, so `T` need not be made an `S`-algebra). The coherences are
`β_id = id` and `β_{χ ∘ φ} = β_χ ∘ β_φ`.

* `DiagramFamily.autMap`: `G_F(φ) : G_F(S) →* G_F(T)`, carrying `g` to the unique automorphism
  `h` of `F_T` with `h ∘ β_φ = β_φ ∘ g`.
* `DiagramFamily.autMap_id`, `DiagramFamily.autMap_comp`, and `DiagramFamily.autFunctor`:
  **`G_F : CAlg_R → Grp` for a family**.
* `DiagramFamily.derMap`, `DiagramFamily.derFunctor`: the same for compatible derivations,
  `g_F : CAlg_R → LieRing`.
* **Families are scalar extensions of one diagram.** `baseChangeFamily F`: every diagram `F` over
  `R` determines the family `S ↦ S ⊗[R] F` with `β_φ = φ ⊗ 1`, whose `G_F` and `g_F` are those of
  `Diagram/Functor.lean` (`baseChangeFamily_autMap`, `baseChangeFamily_derMap`). Conversely,
  `DiagramFamily.baseIso`: for every family, `β_{ι_S}` identifies `F_S` with `S ⊗[R] F_R`, where
  `F_R` is the fiber over the base (`DiagramFamily.base`).
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram

noncomputable section

variable (R : Type u) [CommRing R] (I : Type w) [Category.{w'} I]

/-- A **family of Jordan diagrams over varying base rings**: a diagram `F_S` over every
commutative `R`-algebra `S`, with coherent base-change maps `β_φ : F_S → F_T` for `φ : S → T`. -/
structure DiagramFamily where
  /-- The diagram over `S`. -/
  obj : ∀ S : CommAlgCat.{u'} R, JordanDiagram.{u', v} S I
  /-- The coherence map along `φ : S → T`, `φ`-semilinear. -/
  β : ∀ {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I),
    (obj S).obj i →ₛₗ[φ.hom.toRingHom] (obj T).obj i
  β_mul : ∀ {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I) (x y : (obj S).obj i),
    β φ i (x * y) = β φ i x * β φ i y
  β_naturality : ∀ {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) {i j : I} (α : i ⟶ j)
    (x : (obj S).obj i), β φ j ((obj S).map α x) = (obj T).map α (β φ i x)
  isBaseChange : ∀ {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I), IsSemilinearBaseChange (β φ i)
  β_id : ∀ (S : CommAlgCat.{u'} R) (i : I) (x : (obj S).obj i), β (𝟙 S) i x = x
  β_comp : ∀ {S T U : CommAlgCat.{u'} R} (φ : S ⟶ T) (χ : T ⟶ U) (i : I) (x : (obj S).obj i),
    β (φ ≫ χ) i x = β χ i (β φ i x)

variable {R I}

/-- The arrow `F(α)` of a diagram, as a linear map. -/
def mapLinear {S : Type u'} [CommRing S] (D : JordanDiagram.{u', v} S I) {i j : I} (α : i ⟶ j) :
    D.obj i →ₗ[S] D.obj j where
  toFun := D.map α
  map_add' := map_add _
  map_smul' := map_smul _

namespace DiagramFamily

variable (F : DiagramFamily.{u, u', v} R I)

/-- The automorphism of a node over `T` induced by one over `S`. -/
def nodeAut {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I) (g : jordanAut S ((F.obj S).obj i)) :
    jordanAut T ((F.obj T).obj i) :=
  ⟨(F.isBaseChange φ i).extendEquiv (g : (F.obj S).obj i ≃ₗ[S] (F.obj S).obj i),
    (F.isBaseChange φ i).extend_mul (F.β_mul φ i) (jordanAut.map_mul g)⟩

theorem nodeAut_β {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I)
    (g : jordanAut S ((F.obj S).obj i)) (x : (F.obj S).obj i) :
    F.nodeAut φ i g (F.β φ i x) = F.β φ i (g x) :=
  (F.isBaseChange φ i).extendEquiv_apply _ x

/-- Automorphisms over `T` agree once they agree on the image of `β_φ`. -/
theorem nodeAut_ext {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I)
    {h h' : jordanAut T ((F.obj T).obj i)} (H : ∀ x, h (F.β φ i x) = h' (F.β φ i x)) : h = h' :=
  jordanAut.ext fun y => LinearMap.congr_fun ((F.isBaseChange φ i).ext
    (h := (h : (F.obj T).obj i ≃ₗ[T] (F.obj T).obj i).toLinearMap)
    (h' := (h' : (F.obj T).obj i ≃ₗ[T] (F.obj T).obj i).toLinearMap) H) y

/-- `G_F(φ) : G_F(S) →* G_F(T)` for a family: `g ↦` the unique `h` with `h ∘ β_φ = β_φ ∘ g`. -/
def autMap {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) : (F.obj S).autGroup →* (F.obj T).autGroup where
  toFun g := ⟨fun i => F.nodeAut φ i (g.1 i), fun {i j} α y => by
    have := (F.isBaseChange φ i).ext
      (h := (F.nodeAut φ j (g.1 j) : (F.obj T).obj j ≃ₗ[T] _).toLinearMap ∘ₗ
        mapLinear (F.obj T) α)
      (h' := mapLinear (F.obj T) α ∘ₗ
        (F.nodeAut φ i (g.1 i) : (F.obj T).obj i ≃ₗ[T] _).toLinearMap) fun x => by
      change F.nodeAut φ j (g.1 j) ((F.obj T).map α (F.β φ i x)) =
        (F.obj T).map α (F.nodeAut φ i (g.1 i) (F.β φ i x))
      rw [← F.β_naturality, nodeAut_β, nodeAut_β, autGroup_naturality g α x, F.β_naturality]
    exact LinearMap.congr_fun this y⟩
  map_one' := Subtype.ext (funext fun i => F.nodeAut_ext φ i fun x => by
    rw [nodeAut_β]
    rfl)
  map_mul' g g' := Subtype.ext (funext fun i => F.nodeAut_ext φ i fun x => by
    change F.nodeAut φ i (g.1 i * g'.1 i) (F.β φ i x) =
      F.nodeAut φ i (g.1 i) (F.nodeAut φ i (g'.1 i) (F.β φ i x))
    rw [nodeAut_β, nodeAut_β, nodeAut_β]
    rfl)

theorem autMap_β {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (g : (F.obj S).autGroup) (i : I)
    (x : (F.obj S).obj i) : (F.autMap φ g).1 i (F.β φ i x) = F.β φ i (g.1 i x) :=
  F.nodeAut_β φ i _ x

/-- `G_F(id) = id`. -/
theorem autMap_id (S : CommAlgCat.{u'} R) : F.autMap (𝟙 S) = MonoidHom.id _ :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i => jordanAut.ext fun x => by
    have := F.autMap_β (𝟙 S) g i x
    rwa [F.β_id, F.β_id] at this)

/-- `G_F(χ ∘ φ) = G_F(χ) ∘ G_F(φ)`. -/
theorem autMap_comp {S T U : CommAlgCat.{u'} R} (φ : S ⟶ T) (χ : T ⟶ U) :
    F.autMap (φ ≫ χ) = (F.autMap χ).comp (F.autMap φ) :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i => F.nodeAut_ext (φ ≫ χ) i fun x => by
    change (F.autMap (φ ≫ χ) g).1 i (F.β (φ ≫ χ) i x) =
      (F.autMap χ (F.autMap φ g)).1 i (F.β (φ ≫ χ) i x)
    rw [autMap_β, F.β_comp, F.β_comp, autMap_β, autMap_β])

/-- **`G_F : CAlg_R → Grp` for a family of diagrams**, `S ↦ G_{F_S}(S)`. -/
def autFunctor : CommAlgCat.{u'} R ⥤ GrpCat.{max v w} where
  obj S := GrpCat.of (F.obj S).autGroup
  map φ := GrpCat.ofHom (F.autMap φ)
  map_id S := by
    apply GrpCat.hom_ext
    rw [GrpCat.hom_ofHom, F.autMap_id]
    rfl
  map_comp φ χ := by
    apply GrpCat.hom_ext
    rw [GrpCat.hom_ofHom, F.autMap_comp]
    rfl

/-- The derivation of a node over `T` induced by one over `S`. -/
def nodeDer {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I)
    (D : JordanDerivation S ((F.obj S).obj i)) : JordanDerivation T ((F.obj T).obj i) :=
  ⟨(F.isBaseChange φ i).extend (D : (F.obj S).obj i →ₗ[S] (F.obj S).obj i),
    (F.isBaseChange φ i).extend_leibniz (F.β_mul φ i) D.leibniz⟩

theorem nodeDer_β {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I)
    (D : JordanDerivation S ((F.obj S).obj i)) (x : (F.obj S).obj i) :
    F.nodeDer φ i D (F.β φ i x) = F.β φ i (D x) :=
  (F.isBaseChange φ i).extend_apply _ x

/-- Derivations over `T` agree once they agree on the image of `β_φ`. -/
theorem nodeDer_ext {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (i : I)
    {D E : JordanDerivation T ((F.obj T).obj i)} (H : ∀ x, D (F.β φ i x) = E (F.β φ i x)) :
    D = E :=
  JordanDerivation.ext fun y => LinearMap.congr_fun ((F.isBaseChange φ i).ext
    (h := (D : (F.obj T).obj i →ₗ[T] (F.obj T).obj i))
    (h' := (E : (F.obj T).obj i →ₗ[T] (F.obj T).obj i)) H) y

/-- `g_F(φ) : g_F(S) →⁅⁆ g_F(T)` for a family: `D ↦` the unique `D'` with `D' ∘ β_φ = β_φ ∘ D`,
a homomorphism of Lie rings. -/
def derMap {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    (F.obj S).derAlgebra →⁅⁆ (F.obj T).derAlgebra :=
  ⟨AddMonoidHom.mk' (fun D => ⟨fun i => F.nodeDer φ i (D.1 i), fun {i j} α y => by
      have := (F.isBaseChange φ i).ext
        (h := (F.nodeDer φ j (D.1 j) : (F.obj T).obj j →ₗ[T] (F.obj T).obj j) ∘ₗ
          mapLinear (F.obj T) α)
        (h' := mapLinear (F.obj T) α ∘ₗ
          (F.nodeDer φ i (D.1 i) : (F.obj T).obj i →ₗ[T] (F.obj T).obj i)) fun x => by
        change F.nodeDer φ j (D.1 j) ((F.obj T).map α (F.β φ i x)) =
          (F.obj T).map α (F.nodeDer φ i (D.1 i) (F.β φ i x))
        rw [← F.β_naturality, nodeDer_β, nodeDer_β, D.2 α x, F.β_naturality]
      exact LinearMap.congr_fun this y⟩)
    (fun D E => Subtype.ext (funext fun i => F.nodeDer_ext φ i fun x => by
      change F.nodeDer φ i (D.1 i + E.1 i) (F.β φ i x) =
        F.nodeDer φ i (D.1 i) (F.β φ i x) + F.nodeDer φ i (E.1 i) (F.β φ i x)
      rw [nodeDer_β, nodeDer_β, nodeDer_β, JordanDerivation.add_apply, map_add])),
    fun D E => Subtype.ext (funext fun i => F.nodeDer_ext φ i fun x => by
      change F.nodeDer φ i ⁅D.1 i, E.1 i⁆ (F.β φ i x) =
        ⁅F.nodeDer φ i (D.1 i), F.nodeDer φ i (E.1 i)⁆ (F.β φ i x)
      rw [nodeDer_β, JordanDerivation.lie_apply, JordanDerivation.lie_apply, nodeDer_β,
        nodeDer_β, nodeDer_β, nodeDer_β, map_sub])⟩

theorem derMap_β {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) (D : (F.obj S).derAlgebra) (i : I)
    (x : (F.obj S).obj i) : (F.derMap φ D).1 i (F.β φ i x) = F.β φ i (D.1 i x) :=
  F.nodeDer_β φ i _ x

/-- `g_F(id) = id`. -/
theorem derMap_id (S : CommAlgCat.{u'} R) : F.derMap (𝟙 S) = LieRingHom.id :=
  LieRingHom.ext fun D => Subtype.ext (funext fun i => JordanDerivation.ext fun x => by
    have := F.derMap_β (𝟙 S) D i x
    rwa [F.β_id, F.β_id] at this)

/-- `g_F(χ ∘ φ) = g_F(χ) ∘ g_F(φ)`. -/
theorem derMap_comp {S T U : CommAlgCat.{u'} R} (φ : S ⟶ T) (χ : T ⟶ U) :
    F.derMap (φ ≫ χ) = (F.derMap χ).comp (F.derMap φ) :=
  LieRingHom.ext fun D => Subtype.ext (funext fun i => F.nodeDer_ext (φ ≫ χ) i fun x => by
    change (F.derMap (φ ≫ χ) D).1 i (F.β (φ ≫ χ) i x) =
      (F.derMap χ (F.derMap φ D)).1 i (F.β (φ ≫ χ) i x)
    rw [derMap_β, F.β_comp, F.β_comp, derMap_β, derMap_β])

/-- **`g_F : CAlg_R → LieRing` for a family of diagrams**, `S ↦ g_{F_S}(S)`. -/
def derFunctor : CommAlgCat.{u'} R ⥤ LieRingCat.{max v w} where
  obj S := LieRingCat.of (F.obj S).derAlgebra
  map φ := LieRingCat.ofHom (F.derMap φ)
  map_id S := by
    apply LieRingCat.hom_ext
    rw [LieRingCat.hom_ofHom, F.derMap_id]
    rfl
  map_comp φ χ := by
    apply LieRingCat.hom_ext
    rw [LieRingCat.hom_ofHom, F.derMap_comp]
    rfl

end DiagramFamily

/-! ### The family of scalar extensions of one diagram -/

section BaseChangeFamily

variable [Invertible (2 : R)] (F : JordanDiagram.{u, v} R I)

/-- `φ ⊗ 1 : S ⊗[R] A → T ⊗[R] A`, as a `φ`-semilinear map. -/
def tensorMapSL {A : Type v} [JordanAlgebra R A] {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    S ⊗[R] A →ₛₗ[φ.hom.toRingHom] T ⊗[R] A where
  toFun := tensorMap A φ.hom
  map_add' := map_add _
  map_smul' := tensorMap_smul φ.hom

omit [Invertible (2 : R)] in
/-- `φ ⊗ 1` is a base change: `T ⊗_S (S ⊗_R A) ≅ T ⊗_R A`. -/
theorem isSemilinearBaseChange_tensorMap {A : Type v} [JordanAlgebra R A]
    {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    IsSemilinearBaseChange (tensorMapSL (A := A) φ) := by
  intro P _ _ g
  let _ : Module R P := Module.compHom P (algebraMap R T)
  have _ : IsScalarTower R T P := ⟨fun r t p => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have e : ∀ (s : S) (a : A), s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) := fun s a => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let g' : A →ₗ[R] P :=
    { toFun := fun a => g ((1 : S) ⊗ₜ a)
      map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun r a => by
        change g ((1 : S) ⊗ₜ[R] (r • a)) = algebraMap R T r • g ((1 : S) ⊗ₜ a)
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, e, map_smulₛₗ]
        exact congrArg (· • g ((1 : S) ⊗ₜ a)) (φ.hom.commutes r) }
  refine ⟨LinearMap.liftBaseChange T g', fun x => ?_, fun h' hh' => ?_⟩
  · induction x with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul s a =>
      change LinearMap.liftBaseChange T g' (φ.hom s ⊗ₜ a) = g (s ⊗ₜ a)
      rw [LinearMap.liftBaseChange_tmul, e s a, map_smulₛₗ]
      rfl
  · refine ext_one_tmul fun a => ?_
    rw [LinearMap.liftBaseChange_tmul, one_smul, ← tensorMap_one_tmul φ.hom a]
    exact hh' _

/-- The family of scalar extensions `S ↦ S ⊗[R] F` of a diagram over `R`, with `β_φ = φ ⊗ 1`. -/
def baseChangeFamily : DiagramFamily R I where
  obj S := F.baseChange S
  β φ _ := tensorMapSL φ
  β_mul φ _ := tensorMap_mul φ.hom
  β_naturality φ _ _ α x := tensorMap_baseChangeHom φ.hom (F.map α) x
  isBaseChange φ _ := isSemilinearBaseChange_tensorMap φ
  β_id S _ x := by
    change tensorMap _ (𝟙 S : S ⟶ S).hom x = x
    rw [CommAlgCat.hom_id]
    exact tensorMap_id x
  β_comp φ χ _ x := by
    change tensorMap _ (φ ≫ χ).hom x = _
    rw [CommAlgCat.hom_comp]
    exact tensorMap_comp φ.hom χ.hom x

theorem baseChangeFamily_obj (S : CommAlgCat.{u'} R) :
    (baseChangeFamily F).obj S = F.baseChange S := rfl

/-- The family `S ↦ S ⊗[R] F` has the `G_F` of `Diagram/Functor.lean`. -/
theorem baseChangeFamily_autMap {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    (baseChangeFamily F).autMap φ = autMap F φ.hom :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i =>
    (baseChangeFamily F).nodeAut_ext φ i fun x => by
      rw [DiagramFamily.autMap_β]
      exact (mapAut_tensorMap φ.hom (g.1 i) x).symm)

/-- The family `S ↦ S ⊗[R] F` has the `g_F` of `Diagram/Functor.lean`. -/
theorem baseChangeFamily_derMap {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    (baseChangeFamily F).derMap φ = derMap F φ.hom :=
  LieRingHom.ext fun D => Subtype.ext (funext fun i =>
    (baseChangeFamily F).nodeDer_ext φ i fun x => by
      rw [DiagramFamily.derMap_β]
      exact (mapLin_tensorMap φ.hom _ x).symm)

end BaseChangeFamily

/-! ### Every family is the scalar extension of its fiber over `R` -/

section Base

variable (R) in
/-- The structure map `ι_S : R → S` of an `R`-algebra, as a morphism of `CAlg_R`. -/
def unitHom (S : CommAlgCat.{u} R) : CommAlgCat.of R R ⟶ S :=
  CommAlgCat.ofHom (Algebra.ofId R S)

/-- `a ↦ 1 ⊗ a : A → S ⊗[R] A`, as an `ι_S`-semilinear map. -/
def inclSL (A : Type v) [JordanAlgebra R A] (S : CommAlgCat.{u} R) :
    A →ₛₗ[(unitHom R S).hom.toRingHom] S ⊗[R] A where
  toFun a := (1 : S) ⊗ₜ a
  map_add' a b := TensorProduct.tmul_add _ _ _
  map_smul' r a := by
    change (1 : S) ⊗ₜ[R] (r • a) = algebraMap R S r • ((1 : S) ⊗ₜ[R] a)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one]

/-- `A → S ⊗[R] A` is a base change along `ι_S`. -/
theorem isSemilinearBaseChange_inclSL (A : Type v) [JordanAlgebra R A] (S : CommAlgCat.{u} R) :
    IsSemilinearBaseChange (inclSL A S) := by
  intro P _ _ g
  let _ : Module R P := Module.compHom P (algebraMap R S)
  have _ : IsScalarTower R S P := ⟨fun r t p => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let g' : A →ₗ[R] P :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun r a => map_smulₛₗ g r a }
  refine ⟨LinearMap.liftBaseChange S g', fun a => ?_, fun h' hh' => ?_⟩
  · change LinearMap.liftBaseChange S g' ((1 : S) ⊗ₜ a) = g a
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  · refine ext_one_tmul fun a => ?_
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    exact hh' a

namespace DiagramFamily

variable [Invertible (2 : R)] (F : DiagramFamily.{u, u, max u v} R I)

/-- The fiber of a family over the base ring `R`, as a diagram over `R`. -/
def base : JordanDiagram.{u, max u v} R I := F.obj (CommAlgCat.of R R)

/-- The linear node isomorphism `S ⊗[R] F_R(i) ≅ F_S(i)` induced by `β_{ι_S}`. -/
def baseNodeLin (S : CommAlgCat.{u} R) (i : I) : S ⊗[R] (F.base).obj i ≃ₗ[S] (F.obj S).obj i :=
  (isSemilinearBaseChange_inclSL ((F.base).obj i) S).equiv (F.isBaseChange (unitHom R S) i)

omit [Invertible (2 : R)] in
theorem baseNodeLin_one_tmul (S : CommAlgCat.{u} R) (i : I) (a : (F.base).obj i) :
    F.baseNodeLin S i ((1 : S) ⊗ₜ a) = F.β (unitHom R S) i a :=
  IsSemilinearBaseChange.equiv_apply _ _ a

/-- The node isomorphism `S ⊗[R] F_R(i) ≅ F_S(i)` of Jordan algebras. -/
def baseNodeEquiv (S : CommAlgCat.{u} R) (i : I) :
    S ⊗[R] (F.base).obj i ≃ⱼ[S] (F.obj S).obj i :=
  ⟨F.baseNodeLin S i, (isSemilinearBaseChange_inclSL ((F.base).obj i) S).mul_ext
    (h := (F.baseNodeLin S i).toLinearMap) (fun a b => by
      have hab : ((1 : S) ⊗ₜ[R] a) * ((1 : S) ⊗ₜ[R] b) = (1 : S) ⊗ₜ[R] (a * b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      calc F.baseNodeLin S i (((1 : S) ⊗ₜ[R] a) * ((1 : S) ⊗ₜ[R] b))
          = F.β (unitHom R S) i (a * b) := by rw [hab, baseNodeLin_one_tmul]
        _ = F.β (unitHom R S) i a * F.β (unitHom R S) i b := F.β_mul _ i a b
        _ = F.baseNodeLin S i ((1 : S) ⊗ₜ[R] a) * F.baseNodeLin S i ((1 : S) ⊗ₜ[R] b) := by
          rw [baseNodeLin_one_tmul, baseNodeLin_one_tmul])⟩

theorem baseNodeEquiv_one_tmul (S : CommAlgCat.{u} R) (i : I) (a : (F.base).obj i) :
    F.baseNodeEquiv S i ((1 : S) ⊗ₜ a) = F.β (unitHom R S) i a :=
  F.baseNodeLin_one_tmul S i a

/-- **Every family is a scalar extension of its fiber over the base**: `β_{ι_S}` identifies
`F_S` with `S ⊗[R] F_R`, as diagrams. -/
def baseIso (S : CommAlgCat.{u} R) : DiagramIso ((F.base).baseChange S) (F.obj S) :=
  ⟨F.baseNodeEquiv S, fun {i j} α x => by
    have := (isSemilinearBaseChange_inclSL ((F.base).obj i) S).ext
      (h := (F.baseNodeEquiv S j).toLinearEquiv.toLinearMap ∘ₗ
        mapLinear ((F.base).baseChange S) α)
      (h' := mapLinear (F.obj S) α ∘ₗ (F.baseNodeEquiv S i).toLinearEquiv.toLinearMap)
      fun a => by
        change F.baseNodeEquiv S j ((1 : S) ⊗ₜ (F.base).map α a) =
          (F.obj S).map α (F.baseNodeEquiv S i ((1 : S) ⊗ₜ a))
        rw [baseNodeEquiv_one_tmul, baseNodeEquiv_one_tmul]
        exact F.β_naturality (unitHom R S) α a
    exact LinearMap.congr_fun this x⟩

theorem baseIso_one_tmul (S : CommAlgCat.{u} R) (i : I) (a : (F.base).obj i) :
    (F.baseIso S).app i ((1 : S) ⊗ₜ a) = F.β (unitHom R S) i a :=
  F.baseNodeEquiv_one_tmul S i a

end DiagramFamily

end Base

end

end JordanDiagram
