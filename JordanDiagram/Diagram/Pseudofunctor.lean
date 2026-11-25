module

public import JordanDiagram.Diagram.BaseChange
public import JordanDiagram.Algebra.Dyadic
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import JordanDiagram.MathlibMissing.GrothendieckCocartesian
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Diagrams over varying shapes and base rings form a pseudofunctor

Write `Cat₊` (`TPCat`) for the category of terminally pointed small categories and functors
preserving the chosen terminal object, and `CAlg_{Z[1/2]}` for `CommAlgCat Z[1/2]`.

* `JordanDiagram.category`: the diagrams `I → Jord_R` form a category, with natural
  transformations as morphisms; these are the fibers of the Grothendieck construction.
* `JordanDiagram.restrictFunctor`: restriction along a functor of shapes; it is **strictly**
  functorial (`restrictFunctor_id`, `restrictFunctor_comp`), giving the functor
  `restrictionFunctor R : Cat₊ᵒᵖ ⥤ Cat`.
* `JordanDiagram.isFibered_restriction`: for fixed `R`, the Grothendieck construction of
  restriction is a **fibration** over `Cat₊`.
* `JordanDiagram.baseChangeFunctor`: scalar extension `F ↦ S ⊗[R] F`, which commutes strictly with
  restriction (`restrictFunctor_comp_baseChangeFunctor`); it is functorial up to the coherences
  `baseChangeComp : (− ⊗_R S) ⊗_S T ≅ − ⊗_R T` and `baseChangeId : − ⊗_R R ≅ −`, which satisfy
  the associativity and unit laws (`compHom_assoc`, `compHom_idHom`, `idHom_compHom`).
* `JordanDiagram.baseChangePseudofunctor`: for a fixed shape, **scalar extension is a pseudofunctor**
  `CAlg_{Z[1/2]} → Cat`.
* `JordanDiagram.exists_isStronglyCocartesian_baseChange`: for a fixed shape its Grothendieck
  construction is an **opfibration** over `CAlg_{Z[1/2]}`, the lifts being `F ⟶ S ⊗[R] F`. Mathlib
  has no class of opfibrations, so this is stated as the existence of strongly cocartesian lifts
  (`JordanDiagram/MathlibMissing/GrothendieckCocartesian.lean`).
* `JordanDiagram.diagramPseudofunctor`: **`D : Cat₊ᵒᵖ × CAlg_{Z[1/2]} → Cat`,
  `(I, R) ↦ Fun(I, Jord_R)`, is a pseudofunctor**, acting on `(u, f)` by `F ↦ S ⊗[R] u*F`.
-/

@[expose] public section

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram

section Category

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]

/-- A morphism of diagrams `F → F'` over the same shape and base ring: a natural transformation,
with Jordan homomorphisms as components. -/
@[ext]
structure Hom (F F' : JordanDiagram.{u, v} R I) where
  /-- The component at a node. -/
  app : ∀ i, F.obj i →ₙₐ[R] F'.obj i
  naturality : ∀ {i j : I} (α : i ⟶ j) (x : F.obj i), app j (F.map α x) = F'.map α (app i x)

/-- **The diagrams `I → Jord_R` form a category**, with natural transformations as morphisms. -/
instance category : Category.{max v w} (JordanDiagram.{u, v} R I) where
  Hom := Hom
  id F := ⟨fun i => NonUnitalAlgHom.id R (F.obj i), fun _ _ => rfl⟩
  comp θ θ' := ⟨fun i => (θ'.app i).comp (θ.app i), fun α x => by
    rw [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.comp_apply, θ.naturality, θ'.naturality]⟩

@[ext]
theorem hom_ext {F F' : JordanDiagram.{u, v} R I} {θ θ' : F ⟶ F'}
    (h : ∀ i x, Hom.app θ i x = Hom.app θ' i x) : θ = θ' :=
  Hom.ext (funext fun i => NonUnitalAlgHom.ext (h i))

@[simp]
theorem id_app (F : JordanDiagram.{u, v} R I) (i : I) (x : F.obj i) :
    Hom.app (𝟙 F) i x = x := rfl

@[simp]
theorem comp_app {F F' F'' : JordanDiagram.{u, v} R I} (θ : F ⟶ F') (θ' : F' ⟶ F'') (i : I)
    (x : F.obj i) : Hom.app (θ ≫ θ') i x = Hom.app θ' i (Hom.app θ i x) := rfl

end Category

/-! ### Restriction along shapes -/

section Restriction

variable {R : Type u} [CommRing R]

/-- Restriction along a functor of shapes, as a functor between categories of diagrams. -/
def restrictFunctor {I : Type w} [Category.{w'} I] {I' : Type*} [Category I'] (u : I' ⥤ I) :
    JordanDiagram.{u, v} R I ⥤ JordanDiagram.{u, v} R I' where
  obj F := F.restrict u
  map θ := ⟨fun j => Hom.app θ (u.obj j), fun α x => Hom.naturality θ (u.map α) x⟩

/-- **Restriction is strictly unital.** -/
theorem restrictFunctor_id (I : Type w) [Category.{w'} I] :
    (restrictFunctor (𝟭 I) : JordanDiagram.{u, v} R I ⥤ _) = 𝟭 _ := rfl

/-- **Restriction is strictly functorial.** -/
theorem restrictFunctor_comp {I : Type w} [Category.{w'} I] {I' I'' : Type*} [Category I']
    [Category I''] (p : I'' ⥤ I') (p' : I' ⥤ I) :
    (restrictFunctor (p ⋙ p') : JordanDiagram.{u, v} R I ⥤ _) =
      restrictFunctor p' ⋙ restrictFunctor p := rfl

end Restriction

end JordanDiagram

/-- A terminally pointed small category: an object of `Cat₊`. -/
structure TPCat where
  /-- The underlying type of objects. -/
  carrier : Type w
  [str : Category.{w'} carrier]
  [tp : TerminallyPointed carrier]

attribute [instance] TPCat.str TPCat.tp

namespace TPCat

/-- **`Cat₊`**: terminally pointed small categories and functors preserving the chosen terminal
object. -/
instance category : Category.{max w w'} TPCat.{w, w'} where
  Hom I I' := { u : I.carrier ⥤ I'.carrier // u.obj top = top }
  id I := ⟨𝟭 _, rfl⟩
  comp u v := ⟨u.1 ⋙ v.1, by rw [Functor.comp_obj, u.2, v.2]⟩

end TPCat

namespace JordanDiagram

variable (R : Type u) [CommRing R]

/-- For a fixed base ring, restriction is a functor `Cat₊ᵒᵖ ⥤ Cat`, `I ↦ Fun(I, Jord_R)`. -/
def restrictionFunctor : TPCat.{w, w'}ᵒᵖ ⥤ Cat.{max v w, max (v + 1) u w w'} where
  obj I := Cat.of (JordanDiagram.{u, v} R I.unop.carrier)
  map u := (restrictFunctor u.unop.1).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **For a fixed base ring, the Grothendieck construction of restriction is a fibration over
`Cat₊`**, with cartesian lifts given by restriction. -/
instance isFibered_restriction :
    (Pseudofunctor.CoGrothendieck.forget
      (restrictionFunctor.{u, v, w, w'} R).toPseudofunctor').IsFibered :=
  inferInstance

end JordanDiagram

/-! ### Scalar extension -/

namespace JordanDiagram

section BaseChangeFunctor

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]

theorem baseChangeHom_naturality (S : Type u) [CommRing S] [Algebra R S]
    {F F' : JordanDiagram.{u, u} R I} (θ : F ⟶ F') {i j : I} (α : i ⟶ j)
    (x : S ⊗[R] F.obj i) :
    baseChangeHom S (Hom.app θ j) ((F.baseChange S).map α x) =
      (F'.baseChange S).map α (baseChangeHom S (Hom.app θ i) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    rw [baseChange_map_tmul, baseChangeHom_tmul, baseChangeHom_tmul, baseChange_map_tmul,
      Hom.naturality]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (I) in
/-- Scalar extension `F ↦ S ⊗[R] F`, as a functor between categories of diagrams. -/
noncomputable def baseChangeFunctor (S : Type u) [CommRing S] [Algebra R S] :
    JordanDiagram.{u, u} R I ⥤ JordanDiagram.{u, u} S I where
  obj F := F.baseChange S
  map θ := ⟨fun i => baseChangeHom S (Hom.app θ i), fun α x => baseChangeHom_naturality S θ α x⟩
  map_id F := by
    ext i x
    induction x using TensorProduct.inductionOn with
    | tmul s a => rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_comp θ θ' := by
    ext i x
    induction x using TensorProduct.inductionOn with
    | tmul s a => rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]

@[simp]
theorem baseChangeFunctor_map_tmul (S : Type u) [CommRing S] [Algebra R S]
    {F F' : JordanDiagram.{u, u} R I} (θ : F ⟶ F') (i : I) (s : S) (a : F.obj i) :
    Hom.app ((baseChangeFunctor I S).map θ) i (s ⊗ₜ a) = s ⊗ₜ Hom.app θ i a := rfl

/-- **Scalar extension commutes strictly with restriction.** -/
theorem restrictFunctor_comp_baseChangeFunctor (S : Type u) [CommRing S] [Algebra R S]
    {I' : Type*} [Category I'] (p : I' ⥤ I) :
    (restrictFunctor p ⋙ baseChangeFunctor I' S : JordanDiagram.{u, u} R I ⥤ _) =
      baseChangeFunctor I S ⋙ restrictFunctor p := rfl

/-! #### The composition coherence `(− ⊗_R S) ⊗_S T ≅ − ⊗_R T` -/

variable (S T : Type u) [CommRing S] [Invertible (2 : S)] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

/-- The component `T ⊗[R] F ≅ T ⊗[S] (S ⊗[R] F)` of the composition coherence, as a morphism. -/
noncomputable def compHom (F : JordanDiagram.{u, u} R I) :
    F.baseChange T ⟶ (F.baseChange S).baseChange T :=
  ⟨fun i => (cancelJordanEquiv R S T (F.obj i)).symm.toHom, fun α x =>
    cancelJordanEquiv_symm_baseChangeHom (F.map α) x⟩

/-- The inverse component `T ⊗[S] (S ⊗[R] F) ≅ T ⊗[R] F`. -/
noncomputable def compInv (F : JordanDiagram.{u, u} R I) :
    (F.baseChange S).baseChange T ⟶ F.baseChange T :=
  ⟨fun i => (cancelJordanEquiv R S T (F.obj i)).toHom, fun α x =>
    cancelJordanEquiv_baseChangeHom (F.map α) x⟩

@[simp]
theorem compHom_app_tmul (F : JordanDiagram.{u, u} R I) (i : I) (t : T) (a : F.obj i) :
    Hom.app (compHom S T F) i (t ⊗ₜ a) = t ⊗ₜ ((1 : S) ⊗ₜ a) := rfl

@[simp]
theorem compInv_app_tmul (F : JordanDiagram.{u, u} R I) (i : I) (t : T) (s : S) (a : F.obj i) :
    Hom.app (compInv S T F) i (t ⊗ₜ (s ⊗ₜ a)) = (s • t) ⊗ₜ a := rfl

theorem compHom_naturality {F F' : JordanDiagram.{u, u} R I} (θ : F ⟶ F') (i : I)
    (x : T ⊗[R] F.obj i) :
    Hom.app (compHom S T F') i (baseChangeHom T (Hom.app θ i) x) =
      baseChangeHom T (baseChangeHom S (Hom.app θ i)) (Hom.app (compHom S T F) i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (I) in
/-- **The composition coherence** `(− ⊗_R S) ⊗_S T ≅ − ⊗_R T`, natural in the diagram. -/
noncomputable def baseChangeComp :
    (baseChangeFunctor I T : JordanDiagram.{u, u} R I ⥤ _) ≅
      baseChangeFunctor I S ⋙ baseChangeFunctor I T :=
  NatIso.ofComponents
    (fun F => ⟨compHom S T F, compInv S T F,
      hom_ext fun i x => JordanEquiv.apply_symm_apply (cancelJordanEquiv R S T (F.obj i)) x,
      hom_ext fun i x => JordanEquiv.symm_apply_apply (cancelJordanEquiv R S T (F.obj i)) x⟩)
    (fun θ => hom_ext fun i x => compHom_naturality S T θ i x)

end BaseChangeFunctor

/-! #### The unit coherence `− ⊗_R R ≅ −` -/

section Unit

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]

omit [Invertible (2 : R)] in
/-- `R ⊗[R] A ≃ A` is multiplicative. -/
theorem lid_mul (A : Type u) [JordanAlgebra R A] (x y : R ⊗[R] A) :
    TensorProduct.lid R A (x * y) = TensorProduct.lid R A x * TensorProduct.lid R A y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]
  | tmul r a =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | tmul s b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul,
        TensorProduct.lid_tmul, smul_mul_smul_comm]

/-- The component `R ⊗[R] F ≅ F` of the unit coherence. -/
noncomputable def idHom (F : JordanDiagram.{u, u} R I) : F.baseChange R ⟶ F :=
  ⟨fun i => (⟨TensorProduct.lid R (F.obj i), lid_mul _⟩ : R ⊗[R] F.obj i ≃ⱼ[R] F.obj i).toHom,
    fun α x => by
      induction x using TensorProduct.inductionOn with
      | tmul r a => exact (map_smul (F.map α) r a).symm
      | add x y hx hy => simp only [map_add, hx, hy]⟩

/-- The inverse component `F ≅ R ⊗[R] F`. -/
noncomputable def idInv (F : JordanDiagram.{u, u} R I) : F ⟶ F.baseChange R :=
  ⟨fun i => (⟨TensorProduct.lid R (F.obj i), lid_mul _⟩ : R ⊗[R] F.obj i ≃ⱼ[R] F.obj i).symm.toHom,
    fun _ _ => rfl⟩

@[simp]
theorem idHom_app_tmul (F : JordanDiagram.{u, u} R I) (i : I) (r : R) (a : F.obj i) :
    Hom.app (idHom F) i (r ⊗ₜ a) = r • a := rfl

@[simp]
theorem idInv_app (F : JordanDiagram.{u, u} R I) (i : I) (a : F.obj i) :
    Hom.app (idInv F) i a = (1 : R) ⊗ₜ a := rfl

theorem idHom_naturality {F F' : JordanDiagram.{u, u} R I} (θ : F ⟶ F') (i : I)
    (x : R ⊗[R] F.obj i) :
    Hom.app (idHom F') i (baseChangeHom R (Hom.app θ i) x) = Hom.app θ i (Hom.app (idHom F) i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => exact (map_smul (Hom.app θ i) r a).symm
  | add x y hx hy => simp only [map_add, hx, hy]

variable (I) in
/-- **The unit coherence** `− ⊗_R R ≅ −`, natural in the diagram. -/
noncomputable def baseChangeId (R : Type u) [CommRing R] [Invertible (2 : R)] :
    baseChangeFunctor I R ≅ 𝟭 (JordanDiagram.{u, u} R I) :=
  NatIso.ofComponents
    (fun F => ⟨idHom F, idInv F,
      hom_ext fun i x => (TensorProduct.lid R (F.obj i)).symm_apply_apply x,
      hom_ext fun i x => (TensorProduct.lid R (F.obj i)).apply_symm_apply x⟩)
    (fun θ => hom_ext fun i x => idHom_naturality θ i x)

variable (I) in
/-- The unit coherence, preceded by the (strictly trivial) restriction along `𝟭 I`. -/
noncomputable def restrictBaseChangeId (R : Type u) [CommRing R] [Invertible (2 : R)] :
    restrictFunctor (𝟭 I) ⋙ baseChangeFunctor I R ≅ 𝟭 (JordanDiagram.{u, u} R I) :=
  NatIso.ofComponents
    (fun F => ⟨idHom F, idInv F,
      hom_ext fun i x => (TensorProduct.lid R (F.obj i)).symm_apply_apply x,
      hom_ext fun i x => (TensorProduct.lid R (F.obj i)).apply_symm_apply x⟩)
    (fun θ => hom_ext fun i x => idHom_naturality θ i x)

end Unit

/-! #### The coherence axioms, elementwise -/

section Coherence

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]

/-- **Associativity of the composition coherence**, for `R → S → T → U`. -/
theorem compHom_assoc (S T U : Type u) [CommRing S] [Invertible (2 : S)] [CommRing T]
    [Invertible (2 : T)] [CommRing U] [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S T]
    [Algebra S U] [Algebra T U] [IsScalarTower R S T] [IsScalarTower R T U] [IsScalarTower S T U]
    [IsScalarTower R S U] (F : JordanDiagram.{u, u} R I) (i : I) (x : U ⊗[R] F.obj i) :
    Hom.app (compInv S U F) i (Hom.app (compInv T U (F.baseChange S)) i
      (baseChangeHom U (Hom.app (compHom S T F) i) (Hom.app (compHom T U F) i x))) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    change ((1 : S) • (1 : T) • t) ⊗ₜ a = t ⊗ₜ a
    rw [one_smul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The left unit law**: `R ⊗[R] −` followed by `− ⊗_R T` is `− ⊗_R T`. -/
theorem compHom_idHom (T : Type u) [CommRing T] [Algebra R T] (F : JordanDiagram.{u, u} R I)
    (i : I) (x : T ⊗[R] F.obj i) :
    baseChangeHom T (Hom.app (idHom F) i) (Hom.app (compHom R T F) i x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    change t ⊗ₜ ((1 : R) • a) = t ⊗ₜ a
    rw [one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The right unit law**: `− ⊗_R S` followed by `S ⊗[S] −` is `− ⊗_R S`. -/
theorem idHom_compHom (S : Type u) [CommRing S] [Invertible (2 : S)] [Algebra R S]
    (F : JordanDiagram.{u, u} R I) (i : I) (x : S ⊗[R] F.obj i) :
    Hom.app (idHom (F.baseChange S)) i (Hom.app (compHom S S F) i x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    change s • ((1 : S) ⊗ₜ[R] a) = s ⊗ₜ a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

end Coherence

/-! #### The pseudofunctor on `CAlg_{Z[1/2]}` -/

/-- `2` is invertible in every `Z[1/2]`-algebra. -/
@[reducible] noncomputable def invertibleTwo (S : Type*) [CommRing S] [Algebra ZHalf S] :
    Invertible (2 : S) :=
  have h : (2 : S) * algebraMap ZHalf S (IsLocalization.Away.invSelf (S := ZHalf) (2 : ℤ)) = 1 := by
    rw [← map_ofNat (algebraMap ZHalf S) 2, ← map_mul, ← map_ofNat (algebraMap ℤ ZHalf) 2,
      IsLocalization.Away.mul_invSelf, map_one]
  ⟨algebraMap ZHalf S (IsLocalization.Away.invSelf (S := ZHalf) (2 : ℤ)), by rw [mul_comm, h], h⟩

attribute [local instance] invertibleTwo

variable (I : Type w) [Category.{w'} I]

/-- **Scalar extension of diagrams is a pseudofunctor** `CAlg_{Z[1/2]} → Cat`,
`S ↦ Fun(I, Jord_S)`, with the composition and unit coherences `baseChangeComp`,
`baseChangeId`. -/
noncomputable def baseChangePseudofunctor :
    Pseudofunctor (LocallyDiscrete (CommAlgCat.{u} ZHalf)) Cat.{max u w, max (u + 1) w w'} :=
  LocallyDiscrete.mkPseudofunctor
    (fun S => Cat.of (JordanDiagram.{u, u} S I))
    (fun {S T} φ => letI := φ.hom.toRingHom.toAlgebra; (baseChangeFunctor I T).toCatHom)
    (fun S => Cat.Hom.isoMk (baseChangeId I S))
    (fun {R S T} φ ψ =>
      letI := φ.hom.toRingHom.toAlgebra
      letI := ψ.hom.toRingHom.toAlgebra
      letI := (φ ≫ ψ).hom.toRingHom.toAlgebra
      haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
      Cat.Hom.isoMk (baseChangeComp I S T))
    (by
      intro R S T U f g h
      ext1
      ext F
      refine hom_ext fun i x => ?_
      let := f.hom.toRingHom.toAlgebra
      let := g.hom.toRingHom.toAlgebra
      let := h.hom.toRingHom.toAlgebra
      let := (f ≫ g).hom.toRingHom.toAlgebra
      let := (g ≫ h).hom.toRingHom.toAlgebra
      let := ((f ≫ g) ≫ h).hom.toRingHom.toAlgebra
      have : IsScalarTower R S T := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower R T U := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower S T U := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower R S U := .of_algebraMap_eq fun _ => rfl
      exact compHom_assoc S T U F i x)
    (by
      intro R S f
      ext1
      ext F
      refine hom_ext fun i x => ?_
      let := f.hom.toRingHom.toAlgebra
      exact compHom_idHom S F i x)
    (by
      intro R S f
      ext1
      ext F
      refine hom_ext fun i x => ?_
      let := f.hom.toRingHom.toAlgebra
      exact idHom_compHom S F i x)

open Pseudofunctor.Grothendieck in
/-- **For a fixed shape, the Grothendieck construction of scalar extension is an opfibration over
`CAlg_{Z[1/2]}`**: every base map `f : R ⟶ S` out of the base ring of a diagram `F` has a strongly
cocartesian lift, namely `F ⟶ S ⊗[R] F`. -/
theorem exists_isStronglyCocartesian_baseChange (a : ∫ baseChangePseudofunctor.{u, w, w'} I)
    {S : CommAlgCat.{u} ZHalf} (f : a.base ⟶ S) :
    ∃ (b : ∫ baseChangePseudofunctor I) (φ : a ⟶ b),
      (forget (baseChangePseudofunctor I)).IsStronglyCocartesian f φ :=
  exists_isStronglyCocartesian a f

/-! #### The pseudofunctor `D` on `Cat₊ᵒᵖ × CAlg_{Z[1/2]}` -/

/-- The action `F ↦ S ⊗[R] u*F` of a morphism `(u, f) : (I, R) → (I', S)`. -/
noncomputable def diagramMap {X Y : TPCat.{w, w'}ᵒᵖ × CommAlgCat.{u} ZHalf} (f : X ⟶ Y) :
    JordanDiagram.{u, u} X.2 X.1.unop.carrier ⥤ JordanDiagram.{u, u} Y.2 Y.1.unop.carrier :=
  letI := f.2.hom.toRingHom.toAlgebra
  restrictFunctor f.1.unop.1 ⋙ baseChangeFunctor Y.1.unop.carrier Y.2

/-- **`D : Cat₊ᵒᵖ × CAlg_{Z[1/2]} → Cat`, `(I, R) ↦ Fun(I, Jord_R)`, is a pseudofunctor**:
contravariant in the shape by restriction, covariant in the base ring by scalar extension. A
morphism `(u, f) : (I, R) → (I', S)` acts by `F ↦ S ⊗[R] u*F`. Restriction is strict and commutes
strictly with scalar extension, so the coherences are those of `baseChangePseudofunctor`. -/
noncomputable def diagramPseudofunctor :
    Pseudofunctor (LocallyDiscrete (TPCat.{w, w'}ᵒᵖ × CommAlgCat.{u} ZHalf))
      Cat.{max u w, max (u + 1) w w'} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (JordanDiagram.{u, u} X.2 X.1.unop.carrier))
    (fun f => (diagramMap f).toCatHom)
    (fun X => Cat.Hom.isoMk (restrictBaseChangeId X.1.unop.carrier X.2))
    (fun {X Y Z} f g =>
      letI := f.2.hom.toRingHom.toAlgebra
      letI := g.2.hom.toRingHom.toAlgebra
      letI := (f.2 ≫ g.2).hom.toRingHom.toAlgebra
      haveI : IsScalarTower X.2 Y.2 Z.2 := IsScalarTower.of_algebraMap_eq fun _ => rfl
      Cat.Hom.isoMk (Functor.isoWhiskerLeft (restrictFunctor (g.1.unop.1 ⋙ f.1.unop.1))
        (baseChangeComp Z.1.unop.carrier Y.2 Z.2)))
    (by
      intro X Y Z W f g h
      ext1
      ext F
      refine hom_ext fun i x => ?_
      let := f.2.hom.toRingHom.toAlgebra
      let := g.2.hom.toRingHom.toAlgebra
      let := h.2.hom.toRingHom.toAlgebra
      let := (f.2 ≫ g.2).hom.toRingHom.toAlgebra
      let := (g.2 ≫ h.2).hom.toRingHom.toAlgebra
      let := ((f.2 ≫ g.2) ≫ h.2).hom.toRingHom.toAlgebra
      have : IsScalarTower X.2 Y.2 Z.2 := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower X.2 Z.2 W.2 := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower Y.2 Z.2 W.2 := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower X.2 Y.2 W.2 := .of_algebraMap_eq fun _ => rfl
      exact compHom_assoc Y.2 Z.2 W.2 F _ x)
    (by
      intro X Y f
      ext1
      ext F
      refine hom_ext fun i x => ?_
      let := f.2.hom.toRingHom.toAlgebra
      exact compHom_idHom Y.2 F _ x)
    (by
      intro X Y f
      ext1
      ext F
      refine hom_ext fun i x => ?_
      let := f.2.hom.toRingHom.toAlgebra
      exact idHom_compHom Y.2 (F.restrict f.1.unop.1) i x)

end JordanDiagram
