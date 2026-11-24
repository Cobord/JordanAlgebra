module

public import JordanDiagram.Algebra.Automorphism

/-!
# Jordan isomorphisms between different algebras

`A ≃ⱼ[R] B` (`JordanEquiv`): `R`-linear bijections preserving the Jordan product. These are the
isomorphisms of `Jord_R`. `jordanAut R A` is the group of such self-maps (`toAut`, `ofAut`).

`JordanEquiv.lift`: lifting along injective homomorphisms `ν : A →ₙₐ J`, `ν' : A' →ₙₐ J'`. A
Jordan isomorphism `h : J ≃ⱼ J'` with `h(range ν) = range ν'` transports to a unique
`g : A ≃ⱼ A'` with `ν' ∘ g = h ∘ ν`. This is the input for terminal determination of diagram
isomorphisms and of shape-twisted automorphisms.
-/

@[expose] public section

namespace JordanAlgebra

variable {R : Type*} [CommRing R]

/-- A Jordan isomorphism: an `R`-linear bijection preserving the product. -/
structure JordanEquiv (R A B : Type*) [CommRing R] [JordanAlgebra R A] [JordanAlgebra R B]
    extends A ≃ₗ[R] B where
  map_mul' : ∀ x y, toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y

@[inherit_doc] notation:25 A " ≃ⱼ[" R "] " B => JordanEquiv R A B

namespace JordanEquiv

variable {A B C : Type*} [JordanAlgebra R A] [JordanAlgebra R B] [JordanAlgebra R C]

instance : CoeFun (A ≃ⱼ[R] B) (fun _ => A → B) := ⟨fun e => e.toLinearEquiv⟩

@[simp]
theorem coe_toLinearEquiv (e : A ≃ⱼ[R] B) : ⇑e.toLinearEquiv = e := rfl

theorem map_mul (e : A ≃ⱼ[R] B) (x y : A) : e (x * y) = e x * e y := e.map_mul' x y

theorem injective (e : A ≃ⱼ[R] B) : Function.Injective e := e.toLinearEquiv.injective

theorem bijective (e : A ≃ⱼ[R] B) : Function.Bijective e := e.toLinearEquiv.bijective

@[ext]
theorem ext {e f : A ≃ⱼ[R] B} (h : ∀ x, e x = f x) : e = f := by
  obtain ⟨e, he⟩ := e
  obtain ⟨f, hf⟩ := f
  congr
  exact LinearEquiv.ext h

/-- The identity. -/
@[refl]
def refl (R A : Type*) [CommRing R] [JordanAlgebra R A] : A ≃ⱼ[R] A :=
  ⟨LinearEquiv.refl R A, fun _ _ => rfl⟩

/-- The inverse. -/
@[symm]
def symm (e : A ≃ⱼ[R] B) : B ≃ⱼ[R] A :=
  ⟨e.toLinearEquiv.symm, fun x y => by
    apply e.injective
    change e.toLinearEquiv (e.toLinearEquiv.symm (x * y)) =
      e.toLinearEquiv (e.toLinearEquiv.symm x * e.toLinearEquiv.symm y)
    rw [LinearEquiv.apply_symm_apply, coe_toLinearEquiv, map_mul]
    simp only [LinearEquiv.apply_symm_apply]⟩

/-- Composition. -/
@[trans]
def trans (e : A ≃ⱼ[R] B) (f : B ≃ⱼ[R] C) : A ≃ⱼ[R] C :=
  ⟨e.toLinearEquiv.trans f.toLinearEquiv, fun x y => by
    change f (e (x * y)) = f (e x) * f (e y)
    rw [map_mul, map_mul]⟩

@[simp] theorem symm_symm (e : A ≃ⱼ[R] B) : e.symm.symm = e := ext fun _ => rfl

@[simp] theorem refl_apply (x : A) : refl R A x = x := rfl
@[simp] theorem trans_apply (e : A ≃ⱼ[R] B) (f : B ≃ⱼ[R] C) (x : A) :
    e.trans f x = f (e x) := rfl
@[simp] theorem apply_symm_apply (e : A ≃ⱼ[R] B) (x : B) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x
@[simp] theorem symm_apply_apply (e : A ≃ⱼ[R] B) (x : A) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

/-- A Jordan isomorphism as a morphism of `Jord_R`. -/
def toHom (e : A ≃ⱼ[R] B) : A →ₙₐ[R] B where
  toFun := e
  map_smul' := e.toLinearEquiv.map_smul
  map_zero' := e.toLinearEquiv.map_zero
  map_add' := e.toLinearEquiv.map_add
  map_mul' := e.map_mul

@[simp] theorem toHom_apply (e : A ≃ⱼ[R] B) (x : A) : e.toHom x = e x := rfl

/-- A Jordan self-isomorphism as an element of `jordanAut R A`. -/
def toAut (e : A ≃ⱼ[R] A) : jordanAut R A := ⟨e.toLinearEquiv, e.map_mul⟩

/-- An element of `jordanAut R A` as a Jordan self-isomorphism. -/
def ofAut (g : jordanAut R A) : A ≃ⱼ[R] A := ⟨g, jordanAut.map_mul g⟩

@[simp] theorem toAut_apply (e : A ≃ⱼ[R] A) (x : A) : e.toAut x = e x := rfl
@[simp] theorem ofAut_apply (g : jordanAut R A) (x : A) : ofAut g x = g x := rfl

/-- `jordanAut R A` is the type of Jordan self-isomorphisms. -/
def autEquiv : (A ≃ⱼ[R] A) ≃ jordanAut R A where
  toFun := toAut
  invFun := ofAut
  left_inv _ := rfl
  right_inv _ := rfl

theorem image_eq_iff (e : A ≃ⱼ[R] B) {S : Set A} {T : Set B} :
    e '' S = T ↔ ∀ x, e x ∈ T ↔ x ∈ S := by
  constructor
  · rintro rfl x
    exact ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).2 hx
    · intro hy
      refine ⟨e.symm y, (h _).1 ?_, apply_symm_apply e y⟩
      rwa [apply_symm_apply]

section Lift

variable {A' J J' : Type*} [JordanAlgebra R A'] [JordanAlgebra R J] [JordanAlgebra R J']
variable {ν : A →ₙₐ[R] J} {ν' : A' →ₙₐ[R] J'}

/-- Lifting a Jordan isomorphism `h : J ≃ⱼ J'` with `h(range ν) = range ν'` along injective
`ν`, `ν'`. -/
noncomputable def lift (hν : Function.Injective ν) (hν' : Function.Injective ν')
    (h : J ≃ⱼ[R] J') (hS : h '' Set.range ν = Set.range ν') : A ≃ⱼ[R] A' :=
  have hmap : (rangeSubmodule ν).map (h.toLinearEquiv : J →ₗ[R] J') = rangeSubmodule ν' := by
    apply SetLike.coe_injective
    rw [Submodule.map_coe, coe_rangeSubmodule, coe_rangeSubmodule]
    exact hS
  have spec : ∀ x, ν' (((rangeEquiv hν).trans ((h.toLinearEquiv.ofSubmodules _ _ hmap).trans
      (rangeEquiv hν').symm)) x) = h (ν x) := fun x => by
    change ν' ((rangeEquiv hν').symm _) = _
    rw [rangeEquiv_symm_spec]
    rfl
  ⟨(rangeEquiv hν).trans ((h.toLinearEquiv.ofSubmodules _ _ hmap).trans (rangeEquiv hν').symm),
    fun x y => by
      apply hν'
      rw [spec, _root_.map_mul ν x y, _root_.map_mul ν', spec, spec]
      exact h.map_mul _ _⟩

theorem lift_spec (hν : Function.Injective ν) (hν' : Function.Injective ν')
    (h : J ≃ⱼ[R] J') (hS : h '' Set.range ν = Set.range ν') (x : A) :
    ν' (lift hν hν' h hS x) = h (ν x) := by
  change ν' ((rangeEquiv hν').symm _) = _
  rw [rangeEquiv_symm_spec]
  rfl

end Lift

end JordanEquiv

end JordanAlgebra
