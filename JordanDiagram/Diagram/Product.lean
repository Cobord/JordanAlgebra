module

public import JordanDiagram.Diagram.Functor
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Products of base rings

For `R`-algebras `S` and `S'`, the scalar extension along the product `S × S'` splits:
`(S × S') ⊗[R] A ≅ (S ⊗[R] A) × (S' ⊗[R] A)` (`prodTensorEquiv`, Mathlib's `prodLeft`), with
components the transports `tensorMap` along the two projections. Hence:

* `prodAutEquiv`: `Aut_{S × S'}((S × S') ⊗ A) ≃* Aut_S(S ⊗ A) × Aut_{S'}(S' ⊗ A)`, by transport
  along the projections.
* `autMap_prod_bijective` / `autGroupProdEquiv`: for a diagram `F`,
  `G_F(S × S') ≃* G_F(S) × G_F(S')`, the map being `(G_F(fst), G_F(snd))`. So `G_F` preserves
  binary products of base rings, and the finite subgroups of `G_F(S × S')` are those of
  `G_F(S) × G_F(S')`.
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram

noncomputable section

section Algebra

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {A : Type v} [JordanAlgebra R A]
variable {S S' : Type u'} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

variable (A S S') in
/-- `(S × S') ⊗[R] A ≅ (S ⊗[R] A) × (S' ⊗[R] A)`, with components the transports along the
projections. -/
def prodTensorEquiv : (S × S') ⊗[R] A ≃ₗ[R] (S ⊗[R] A) × (S' ⊗[R] A) :=
  TensorProduct.prodLeft R R S S' A

omit [Invertible (2 : R)] in
theorem prodTensorEquiv_apply (x : (S × S') ⊗[R] A) :
    prodTensorEquiv A S S' x =
      (tensorMap A (AlgHom.fst R S S') x, tensorMap A (AlgHom.snd R S S') x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, Prod.mk_add_mk]
  | tmul s a => rfl

omit [Invertible (2 : R)] in
theorem prodTensorEquiv_fst (x : (S × S') ⊗[R] A) :
    (prodTensorEquiv A S S' x).1 = tensorMap A (AlgHom.fst R S S') x := by
  rw [prodTensorEquiv_apply]

omit [Invertible (2 : R)] in
theorem prodTensorEquiv_snd (x : (S × S') ⊗[R] A) :
    (prodTensorEquiv A S S' x).2 = tensorMap A (AlgHom.snd R S S') x := by
  rw [prodTensorEquiv_apply]

omit [Invertible (2 : R)] in
theorem prodTensorEquiv_smul (c : S × S') (x : (S × S') ⊗[R] A) :
    prodTensorEquiv A S S' (c • x) =
      (c.1 • (prodTensorEquiv A S S' x).1, c.2 • (prodTensorEquiv A S S' x).2) := by
  rw [prodTensorEquiv_apply, prodTensorEquiv_apply, tensorMap_smul, tensorMap_smul]
  rfl

omit [Invertible (2 : R)] in
theorem prodTensorEquiv_mul (x y : (S × S') ⊗[R] A) :
    prodTensorEquiv A S S' (x * y) = prodTensorEquiv A S S' x * prodTensorEquiv A S S' y := by
  rw [prodTensorEquiv_apply, prodTensorEquiv_apply, prodTensorEquiv_apply, tensorMap_mul,
    tensorMap_mul]
  rfl

/-- The automorphism of `(S × S') ⊗ A` acting by `g` and `g'` on the two factors. -/
def prodAut (g : jordanAut S (S ⊗[R] A)) (g' : jordanAut S' (S' ⊗[R] A)) :
    jordanAut (S × S') ((S × S') ⊗[R] A) :=
  let e := prodTensorEquiv A S S'
  let L : (S × S') ⊗[R] A ≃ₗ[R] (S × S') ⊗[R] A :=
    (e.trans (LinearEquiv.prodCongr ((g : S ⊗[R] A ≃ₗ[S] S ⊗[R] A).restrictScalars R)
      ((g' : S' ⊗[R] A ≃ₗ[S'] S' ⊗[R] A).restrictScalars R))).trans e.symm
  have hL : ∀ z, e (L z) = (g (e z).1, g' (e z).2) := fun z => e.apply_symm_apply _
  ⟨{ toFun := L
     invFun := L.symm
     map_add' := L.map_add
     map_smul' := fun c x => by
       apply e.injective
       rw [RingHom.id_apply, hL, prodTensorEquiv_smul, prodTensorEquiv_smul, hL]
       exact Prod.ext (LinearEquiv.map_smul (g : S ⊗[R] A ≃ₗ[S] S ⊗[R] A) _ _)
         (LinearEquiv.map_smul (g' : S' ⊗[R] A ≃ₗ[S'] S' ⊗[R] A) _ _)
     left_inv := L.symm_apply_apply
     right_inv := L.apply_symm_apply }, fun x y => by
    change L (x * y) = L x * L y
    apply e.injective
    rw [prodTensorEquiv_mul, hL, hL, hL, prodTensorEquiv_mul]
    exact Prod.ext (jordanAut.map_mul g _ _) (jordanAut.map_mul g' _ _)⟩

theorem prodTensorEquiv_prodAut (g : jordanAut S (S ⊗[R] A)) (g' : jordanAut S' (S' ⊗[R] A))
    (x : (S × S') ⊗[R] A) :
    prodTensorEquiv A S S' (prodAut g g' x) =
      (g (prodTensorEquiv A S S' x).1, g' (prodTensorEquiv A S S' x).2) :=
  (prodTensorEquiv A S S').apply_symm_apply _

theorem tensorMap_fst_prodAut (g : jordanAut S (S ⊗[R] A)) (g' : jordanAut S' (S' ⊗[R] A))
    (x : (S × S') ⊗[R] A) :
    tensorMap A (AlgHom.fst R S S') (prodAut g g' x) = g (tensorMap A (AlgHom.fst R S S') x) := by
  rw [← prodTensorEquiv_fst, prodTensorEquiv_prodAut, prodTensorEquiv_fst]

theorem tensorMap_snd_prodAut (g : jordanAut S (S ⊗[R] A)) (g' : jordanAut S' (S' ⊗[R] A))
    (x : (S × S') ⊗[R] A) :
    tensorMap A (AlgHom.snd R S S') (prodAut g g' x) = g' (tensorMap A (AlgHom.snd R S S') x) := by
  rw [← prodTensorEquiv_snd, prodTensorEquiv_prodAut, prodTensorEquiv_snd]

theorem mapAut_fst_prodAut (g : jordanAut S (S ⊗[R] A)) (g' : jordanAut S' (S' ⊗[R] A)) :
    mapAut (AlgHom.fst R S S') (prodAut g g') = g := by
  refine jordanAut.ext fun x => ?_
  obtain ⟨z, rfl⟩ : ∃ z, tensorMap A (AlgHom.fst R S S') z = x :=
    ⟨(prodTensorEquiv A S S').symm (x, 0), by
      rw [← prodTensorEquiv_fst, LinearEquiv.apply_symm_apply]⟩
  rw [mapAut_tensorMap, tensorMap_fst_prodAut]

theorem mapAut_snd_prodAut (g : jordanAut S (S ⊗[R] A)) (g' : jordanAut S' (S' ⊗[R] A)) :
    mapAut (AlgHom.snd R S S') (prodAut g g') = g' := by
  refine jordanAut.ext fun x => ?_
  obtain ⟨z, rfl⟩ : ∃ z, tensorMap A (AlgHom.snd R S S') z = x :=
    ⟨(prodTensorEquiv A S S').symm (0, x), by
      rw [← prodTensorEquiv_snd, LinearEquiv.apply_symm_apply]⟩
  rw [mapAut_tensorMap, tensorMap_snd_prodAut]

/-- An automorphism of `(S × S') ⊗ A` is determined by its transports to the two factors. -/
theorem eq_of_mapAut_fst_snd {g h : jordanAut (S × S') ((S × S') ⊗[R] A)}
    (h1 : mapAut (AlgHom.fst R S S') g = mapAut (AlgHom.fst R S S') h)
    (h2 : mapAut (AlgHom.snd R S S') g = mapAut (AlgHom.snd R S S') h) : g = h := by
  refine jordanAut.ext fun x => (prodTensorEquiv A S S').injective (Prod.ext ?_ ?_)
  · rw [prodTensorEquiv_fst, prodTensorEquiv_fst, ← mapAut_tensorMap, ← mapAut_tensorMap, h1]
  · rw [prodTensorEquiv_snd, prodTensorEquiv_snd, ← mapAut_tensorMap, ← mapAut_tensorMap, h2]

variable (A S S') in
/-- **Products of base rings, one algebra**: `Aut((S × S') ⊗ A) ≃* Aut(S ⊗ A) × Aut(S' ⊗ A)`,
by transport along the two projections. -/
def prodAutEquiv :
    jordanAut (S × S') ((S × S') ⊗[R] A) ≃* jordanAut S (S ⊗[R] A) × jordanAut S' (S' ⊗[R] A) :=
  MulEquiv.ofBijective ((mapAut (AlgHom.fst R S S')).prod (mapAut (AlgHom.snd R S S')))
    ⟨fun _ _ h => eq_of_mapAut_fst_snd (congrArg Prod.fst h) (congrArg Prod.snd h),
      fun p => ⟨prodAut p.1 p.2, Prod.ext (mapAut_fst_prodAut _ _) (mapAut_snd_prodAut _ _)⟩⟩

end Algebra

section Diagram

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} R I)
variable (S S' : Type u') [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

/-- The diagram automorphism of `(S × S') ⊗ F` acting by `g` and `g'` on the two factors. -/
def prodAutDiagram (g : (F.baseChange S).autGroup) (g' : (F.baseChange S').autGroup) :
    (F.baseChange (S × S')).autGroup :=
  ⟨fun i => prodAut (g.1 i) (g'.1 i), fun {i j} α x => by
    apply (prodTensorEquiv (F.obj j) S S').injective
    refine Prod.ext ?_ ?_
    · rw [prodTensorEquiv_fst, prodTensorEquiv_fst]
      change tensorMap _ _ (prodAut (g.1 j) (g'.1 j) (baseChangeHom (S × S') (F.map α) x)) =
        tensorMap _ _ (baseChangeHom (S × S') (F.map α) (prodAut (g.1 i) (g'.1 i) x))
      rw [tensorMap_fst_prodAut, tensorMap_baseChangeHom, tensorMap_baseChangeHom,
        tensorMap_fst_prodAut]
      exact autGroup_naturality g α _
    · rw [prodTensorEquiv_snd, prodTensorEquiv_snd]
      change tensorMap _ _ (prodAut (g.1 j) (g'.1 j) (baseChangeHom (S × S') (F.map α) x)) =
        tensorMap _ _ (baseChangeHom (S × S') (F.map α) (prodAut (g.1 i) (g'.1 i) x))
      rw [tensorMap_snd_prodAut, tensorMap_baseChangeHom, tensorMap_baseChangeHom,
        tensorMap_snd_prodAut]
      exact autGroup_naturality g' α _⟩

/-- **Products of base rings**: `(G_F(fst), G_F(snd)) : G_F(S × S') → G_F(S) × G_F(S')` is
bijective. -/
theorem autMap_prod_bijective :
    Function.Bijective ((autMap F (AlgHom.fst R S S')).prod (autMap F (AlgHom.snd R S S'))) :=
  ⟨fun _ _ hgh => Subtype.ext (funext fun i => eq_of_mapAut_fst_snd
      (congrArg (fun p => (Prod.fst p).1 i) hgh) (congrArg (fun p => (Prod.snd p).1 i) hgh)),
    fun p => ⟨prodAutDiagram F S S' p.1 p.2, Prod.ext
      (Subtype.ext (funext fun _ => mapAut_fst_prodAut _ _))
      (Subtype.ext (funext fun _ => mapAut_snd_prodAut _ _))⟩⟩

/-- **Products of base rings**: `G_F(S × S') ≃* G_F(S) × G_F(S')`. -/
def autGroupProdEquiv :
    (F.baseChange (S × S')).autGroup ≃* (F.baseChange S).autGroup × (F.baseChange S').autGroup :=
  MulEquiv.ofBijective _ (autMap_prod_bijective F S S')

end Diagram

end

end JordanDiagram
