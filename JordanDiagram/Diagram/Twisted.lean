module

public import JordanDiagram.Diagram.Iso
public import Mathlib.Algebra.Order.Group.End

/-!
# The shape-twisted automorphism group

Let `F` be a Jordan diagram whose shape `I` is a preorder. A *twisted automorphism* of `F`
(`TwistedAut F`) is an order automorphism `σ` of the shape, together with Jordan isomorphisms
`θᵢ : F(i) ≃ F(σ i)` with `θⱼ ∘ F(i ≤ j) = F(σ i ≤ σ j) ∘ θᵢ`. Over a fixed `σ` these are the
twisted isomorphisms `F ≅ σ* F` of `Diagram/Iso.lean` (`TwistedAut.toTwistedIso`).

This is the preorder case, where parallel arrows are equal and order automorphisms are the shape
automorphisms; the wreath-product example uses it. `Diagram/TwistedGeneral.lean` treats arbitrary
terminally pointed shapes.

* `TwistedAut.instGroup`: twisted automorphisms form a group `G̃_F(R)`, with
  `(σ, θ) (τ, η) = (σ τ, θ_τ ∘ η)`.
* `TwistedAut.shapeHom : G̃_F(R) →* Aut(I)` records the shape automorphism.
* `TwistedAut.ofAut : G_F(R) →* G̃_F(R)` views a diagram automorphism as a twisted automorphism
  over the identity. It is injective, and its range is the kernel of `shapeHom`
  (`TwistedAut.range_ofAut`): the sequence `1 → G_F(R) → G̃_F(R) → Aut(I)` is exact.

Over a preorder every pair of parallel arrows is equal, so a node `F(i)` is canonically identified
with `F(j)` when `i = j` (`castEquiv`); this transport is what makes inverses typecheck.
-/

@[expose] public section

universe u v w

open CategoryTheory JordanAlgebra

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Preorder I] (F : JordanDiagram.{u, v} R I)

section Preorder

/-- Over a preorder, parallel arrows act equally. -/
theorem map_congr {i j : I} (f g : i ⟶ j) (x : F.obj i) : F.map f x = F.map g x := by
  rw [Subsingleton.elim f g]

/-- Over a preorder, every endo-arrow acts as the identity. -/
theorem map_self {i : I} (f : i ⟶ i) (x : F.obj i) : F.map f x = x := by
  rw [Subsingleton.elim f (𝟙 i), F.map_id]

/-- Transport between the nodes at equal indices. -/
def castEquiv {i j : I} (h : i = j) : F.obj i ≃ⱼ[R] F.obj j :=
  ⟨{ toFun := F.map (homOfLE h.le)
     invFun := F.map (homOfLE h.ge)
     map_add' := map_add _
     map_smul' := map_smul _
     left_inv := fun x => by rw [← F.map_comp, map_self]
     right_inv := fun x => by rw [← F.map_comp, map_self] },
    fun x y => map_mul (F.map (homOfLE h.le)) x y⟩

theorem castEquiv_apply {i j : I} (h : i = j) (x : F.obj i) :
    F.castEquiv h x = F.map (homOfLE h.le) x := rfl

end Preorder

/-- A **twisted automorphism** of a diagram over a preorder: an order automorphism `σ` of the shape
and Jordan isomorphisms `θᵢ : F(i) ≃ F(σ i)` compatible with the arrows. -/
structure TwistedAut where
  /-- The automorphism of the shape. -/
  shape : I ≃o I
  /-- The component at node `i`. -/
  app : ∀ i, F.obj i ≃ⱼ[R] F.obj (shape i)
  naturality : ∀ {i j : I} (α : i ⟶ j) (x : F.obj i),
    app j (F.map α x) = F.map (homOfLE (shape.monotone (leOfHom α))) (app i x)

namespace TwistedAut

variable {F}

/-- Twisted automorphisms are equal when their shapes agree and their components agree after
transport. -/
theorem ext' {a b : TwistedAut F} (hs : a.shape = b.shape)
    (h : ∀ i x (hi : a.shape i ≤ b.shape i), F.map (homOfLE hi) (a.app i x) = b.app i x) :
    a = b := by
  obtain ⟨sa, appa, na⟩ := a
  obtain ⟨sb, appb, nb⟩ := b
  dsimp only at hs
  subst hs
  congr
  funext i
  exact JordanEquiv.ext fun x => (F.map_self _ _).symm.trans (h i x le_rfl)

/-- Naturality against any arrow between the shifted nodes. -/
theorem naturality' (a : TwistedAut F) {i j : I} (f : i ⟶ j) (g : a.shape i ⟶ a.shape j)
    (x : F.obj i) : a.app j (F.map f x) = F.map g (a.app i x) :=
  (a.naturality f x).trans (F.map_congr _ _ _)

/-- Naturality of the inverse components. -/
theorem symm_naturality (a : TwistedAut F) {i j : I} (f : i ⟶ j) (g : a.shape i ⟶ a.shape j)
    (y : F.obj (a.shape i)) : (a.app j).symm (F.map g y) = F.map f ((a.app i).symm y) := by
  apply (a.app j).injective
  rw [JordanEquiv.apply_symm_apply, a.naturality' f g, JordanEquiv.apply_symm_apply]

/-- The product `(σ, θ) (τ, η) = (σ τ, θ_τ ∘ η)`. -/
instance : Mul (TwistedAut F) where
  mul a b := ⟨a.shape * b.shape, fun i => (b.app i).trans (a.app (b.shape i)), fun α x =>
    (congrArg (a.app _) (b.naturality α x)).trans
      ((a.naturality _ _).trans (F.map_congr _ _ _))⟩

instance : One (TwistedAut F) where
  one := ⟨1, fun _ => JordanEquiv.refl R _, fun _ _ => rfl⟩

/-- The inverse `(σ, θ)⁻¹ = (σ⁻¹, θ_{σ⁻¹}⁻¹)`, after transport along `σ σ⁻¹ i = i`. -/
instance : Inv (TwistedAut F) where
  inv a := ⟨a.shape.symm, fun i =>
    (F.castEquiv (a.shape.apply_symm_apply i).symm).trans (a.app (a.shape.symm i)).symm,
    fun {i j} α x => by
      have h1 : F.castEquiv (a.shape.apply_symm_apply j).symm (F.map α x) =
          F.map (homOfLE (a.shape.monotone (a.shape.symm.monotone (leOfHom α))))
            (F.castEquiv (a.shape.apply_symm_apply i).symm x) := by
        rw [castEquiv_apply, castEquiv_apply, ← F.map_comp, ← F.map_comp]
        exact F.map_congr _ _ _
      change (a.app _).symm (F.castEquiv _ (F.map α x)) =
        F.map _ ((a.app _).symm (F.castEquiv _ x))
      rw [h1]
      exact a.symm_naturality _ _ _⟩

theorem mul_shape (a b : TwistedAut F) : (a * b).shape = a.shape * b.shape := rfl

theorem mul_app (a b : TwistedAut F) (i : I) (x : F.obj i) :
    (a * b).app i x = a.app (b.shape i) (b.app i x) := rfl

theorem one_shape : (1 : TwistedAut F).shape = 1 := rfl

theorem one_app (i : I) (x : F.obj i) : (1 : TwistedAut F).app i x = x := rfl

theorem inv_shape (a : TwistedAut F) : a⁻¹.shape = a.shape⁻¹ := rfl

/-- **The shape-twisted group** `G̃_F(R)`. -/
instance instGroup : Group (TwistedAut F) where
  mul_assoc _ _ _ := ext' rfl fun _ _ _ => F.map_self _ _
  one_mul _ := ext' rfl fun _ _ _ => F.map_self _ _
  mul_one _ := ext' rfl fun _ _ _ => F.map_self _ _
  inv_mul_cancel a := ext' (inv_mul_cancel a.shape) fun i x hi => by
    apply (a.app i).injective
    have := a.naturality' (i := a.shape.symm (a.shape i)) (j := i) (homOfLE hi)
      (homOfLE (a.shape.apply_symm_apply _).le)
      ((a.app (a.shape.symm (a.shape i))).symm
        (F.castEquiv (a.shape.apply_symm_apply (a.shape i)).symm (a.app i x)))
    rw [JordanEquiv.apply_symm_apply, castEquiv_apply, ← F.map_comp, map_self] at this
    exact this

variable (F) in
/-- The shape automorphism of a twisted automorphism, `G̃_F(R) → Aut(I)`. -/
def shapeHom : TwistedAut F →* (I ≃o I) where
  toFun := shape
  map_one' := rfl
  map_mul' _ _ := rfl

theorem shapeHom_apply (a : TwistedAut F) : shapeHom F a = a.shape := rfl

variable (F) in
/-- A diagram automorphism, as a twisted automorphism over the identity. -/
def ofAut : F.autGroup →* TwistedAut F where
  toFun g := ⟨1, fun i => JordanEquiv.ofAut (g.1 i), fun α x => autGroup_naturality g α x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ofAut_app (g : F.autGroup) (i : I) (x : F.obj i) : (ofAut F g).app i x = g.1 i x := rfl

theorem ofAut_injective : Function.Injective (ofAut F) := by
  intro g h hgh
  change (⟨1, fun i => JordanEquiv.ofAut (g.1 i), _⟩ : TwistedAut F) =
    ⟨1, fun i => JordanEquiv.ofAut (h.1 i), _⟩ at hgh
  have happ := eq_of_heq (TwistedAut.mk.inj hgh).2
  apply Subtype.ext
  funext i
  apply jordanAut.ext
  intro x
  exact congrArg (fun f : ∀ i, F.obj i ≃ⱼ[R] F.obj i => f i x) happ

/-- **Exactness of `1 → G_F(R) → G̃_F(R) → Aut(I)`**: the twisted automorphisms over the
identity shape automorphism are exactly the diagram automorphisms. -/
theorem range_ofAut : (ofAut F).range = (shapeHom F).ker := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    rfl
  · intro ha
    have hs : a.shape = 1 := ha
    have hi : ∀ i, a.shape i = i := fun i => by rw [hs]; rfl
    refine ⟨⟨fun i => ((a.app i).trans (F.castEquiv (hi i))).toAut, fun α x => ?_⟩, ?_⟩
    · change F.castEquiv (hi _) (a.app _ (F.map α x)) = F.map α (F.castEquiv (hi _) (a.app _ x))
      rw [a.naturality, castEquiv_apply, castEquiv_apply, ← F.map_comp, ← F.map_comp]
      exact F.map_congr _ _ _
    · refine ext' hs.symm fun i x hi' => ?_
      exact (F.map_comp _ _ _).symm.trans (F.map_self _ _)

/-- The kernel of `G̃_F(R) → Aut(I)` is `G_F(R)`. -/
noncomputable def autGroupEquivKer : F.autGroup ≃* (shapeHom F).ker :=
  (MonoidHom.ofInjective ofAut_injective).trans (MulEquiv.subgroupCongr range_ofAut)

/-- A twisted automorphism over `σ` is a twisted isomorphism `F ≅ σ* F`. -/
def toTwistedIso (a : TwistedAut F) : TwistedIso F a.shape.monotone.functor :=
  ⟨a.app, a.naturality⟩

/-- A twisted isomorphism `F ≅ σ* F` is a twisted automorphism over `σ`. -/
def ofTwistedIso (σ : I ≃o I) (θ : TwistedIso F σ.monotone.functor) : TwistedAut F :=
  ⟨σ, θ.app, θ.naturality⟩

theorem ofTwistedIso_shape (σ : I ≃o I) (θ : TwistedIso F σ.monotone.functor) :
    (ofTwistedIso σ θ).shape = σ := rfl

theorem ofTwistedIso_toTwistedIso (a : TwistedAut F) : ofTwistedIso a.shape a.toTwistedIso = a :=
  rfl

end TwistedAut

end JordanDiagram
