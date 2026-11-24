module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Jordan.JordanAlgebra

/-!
# Base change along a ring homomorphism, by its universal property

For a ring homomorphism `σ : S →+* T`, an `S`-module `M` and a `T`-module `N`, a `σ`-semilinear map
`f : M →ₛₗ[σ] N` *is a base change* (`IsSemilinearBaseChange`) if every `σ`-semilinear map out of
`M` into a `T`-module factors uniquely through a `T`-linear map out of `N`. This is the universal
property of `M → T ⊗_S M`, stated without making `T` an `S`-algebra.

* `lift`, `lift_apply`, `ext`: the factorization and its uniqueness.
* `extend`: an `S`-linear endomorphism `g` of `M` extends uniquely to a `T`-linear endomorphism
  of `N` with `extend g ∘ f = f ∘ g`; `extend_id`, `extend_comp`, and `extendEquiv` for
  automorphisms.
* `extend_mul`: for Jordan algebras (or any algebras whose product is bilinear), if `f` and `g`
  are multiplicative then so is `extend g`.
-/

@[expose] public section

universe v

noncomputable section

variable {S T : Type*} [CommRing S] [CommRing T] {σ : S →+* T}

/-- `f : M →ₛₗ[σ] N` is a base change of `M` along `σ`: every `σ`-semilinear map out of `M` into a
`T`-module factors uniquely through a `T`-linear map out of `N`. -/
def IsSemilinearBaseChange {M : Type*} {N : Type v} [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module T N] (f : M →ₛₗ[σ] N) : Prop :=
  ∀ (P : Type v) [AddCommGroup P] [Module T P] (g : M →ₛₗ[σ] P),
    ∃! h : N →ₗ[T] P, ∀ x, h (f x) = g x

namespace IsSemilinearBaseChange

section General

variable {M : Type*} {N : Type v} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
variable {f : M →ₛₗ[σ] N} (hf : IsSemilinearBaseChange f)
variable {P : Type v} [AddCommGroup P] [Module T P]

/-- The `T`-linear factorization of a `σ`-semilinear map through a base change. -/
def lift (g : M →ₛₗ[σ] P) : N →ₗ[T] P := (hf P g).exists.choose

theorem lift_apply (g : M →ₛₗ[σ] P) (x : M) : hf.lift g (f x) = g x :=
  (hf P g).exists.choose_spec x

include hf in
/-- `T`-linear maps out of a base change are determined on the image of `f`. -/
theorem ext {h h' : N →ₗ[T] P} (H : ∀ x, h (f x) = h' (f x)) : h = h' :=
  (hf P (h'.comp f)).unique (fun x => H x) (fun _ => rfl)

theorem eq_lift (g : M →ₛₗ[σ] P) {h : N →ₗ[T] P} (H : ∀ x, h (f x) = g x) : h = hf.lift g :=
  hf.ext fun x => (H x).trans (hf.lift_apply g x).symm

/-- The extension of an `S`-linear endomorphism `g` of `M` to `N`: `extend g ∘ f = f ∘ g`. -/
def extend (g : M →ₗ[S] M) : N →ₗ[T] N := hf.lift (f.comp g)

theorem extend_apply (g : M →ₗ[S] M) (x : M) : hf.extend g (f x) = f (g x) :=
  hf.lift_apply _ x

theorem extend_id : hf.extend LinearMap.id = LinearMap.id :=
  hf.ext fun x => by rw [extend_apply, LinearMap.id_apply, LinearMap.id_apply]

theorem extend_comp (g g' : M →ₗ[S] M) : hf.extend (g ∘ₗ g') = hf.extend g ∘ₗ hf.extend g' :=
  hf.ext fun x => by
    rw [extend_apply, LinearMap.comp_apply, LinearMap.comp_apply, extend_apply, extend_apply]

/-- The extension of a linear automorphism. -/
def extendEquiv (g : M ≃ₗ[S] M) : N ≃ₗ[T] N :=
  LinearEquiv.ofLinearMap (hf.extend g.toLinearMap) (hf.extend g.symm.toLinearMap)
    (by rw [← extend_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, extend_id])
    (by rw [← extend_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, extend_id])

theorem extendEquiv_apply (g : M ≃ₗ[S] M) (x : M) : hf.extendEquiv g (f x) = f (g x) :=
  hf.extend_apply _ x

variable {N' : Type v} [AddCommGroup N'] [Module T N'] {f' : M →ₛₗ[σ] N'}
  (hf' : IsSemilinearBaseChange f')

/-- **Uniqueness of base change**: two base changes of `M` along `σ` are isomorphic, by the
unique `T`-linear isomorphism compatible with the two maps. -/
def equiv : N ≃ₗ[T] N' :=
  LinearEquiv.ofLinearMap (hf.lift f') (hf'.lift f)
    (hf'.ext fun x => by rw [LinearMap.comp_apply, lift_apply, lift_apply, LinearMap.id_apply])
    (hf.ext fun x => by rw [LinearMap.comp_apply, lift_apply, lift_apply, LinearMap.id_apply])

theorem equiv_apply (x : M) : hf.equiv hf' (f x) = f' x := hf.lift_apply f' x

end General

section Jordan

variable {M : Type*} {N : Type v} [JordanAlgebra S M] [JordanAlgebra T N] {f : M →ₛₗ[σ] N}
  (hf : IsSemilinearBaseChange f)

include hf in
/-- A `T`-linear map out of a base change of Jordan algebras is multiplicative once it is
multiplicative on the image of `f`, since the products are `T`-bilinear. -/
theorem mul_ext {N' : Type v} [JordanAlgebra T N'] {h : N →ₗ[T] N'}
    (H : ∀ a b, h (f a * f b) = h (f a) * h (f b)) (x y : N) :
    h (x * y) = h x * h y := by
  have h1 : ∀ a y, h (f a * y) = h (f a) * h y := fun a y =>
    LinearMap.congr_fun (hf.ext (h := h ∘ₗ LinearMap.mulLeft T (f a))
      (h' := LinearMap.mulLeft T (h (f a)) ∘ₗ h) fun b => H a b) y
  exact LinearMap.congr_fun (hf.ext (h := h ∘ₗ LinearMap.mulRight T y)
    (h' := LinearMap.mulRight T (h y) ∘ₗ h) fun a => h1 a y) x

include hf in
/-- The extension of a multiplicative endomorphism along a multiplicative base change is
multiplicative. -/
theorem extend_mul (hfm : ∀ x y, f (x * y) = f x * f y) {g : M →ₗ[S] M}
    (hg : ∀ x y, g (x * y) = g x * g y) (x y : N) :
    hf.extend g (x * y) = hf.extend g x * hf.extend g y :=
  hf.mul_ext (fun a b => by
    rw [← hfm, extend_apply, extend_apply, extend_apply, hg, hfm]) x y

include hf in
/-- The extension of an `S`-linear derivation along a multiplicative base change satisfies the
Leibniz rule. -/
theorem extend_leibniz (hfm : ∀ x y, f (x * y) = f x * f y) {g : M →ₗ[S] M}
    (hg : ∀ a b, g (a * b) = a * g b + g a * b) (x y : N) :
    hf.extend g (x * y) = x * hf.extend g y + hf.extend g x * y := by
  set h := hf.extend g
  have h1 : ∀ a y, h (f a * y) = f a * h y + h (f a) * y := fun a y =>
    LinearMap.congr_fun (hf.ext (h := h ∘ₗ LinearMap.mulLeft T (f a))
      (h' := LinearMap.mulLeft T (f a) ∘ₗ h + LinearMap.mulLeft T (h (f a))) fun b => by
        change h (f a * f b) = f a * h (f b) + h (f a) * f b
        rw [← hfm, extend_apply, extend_apply, extend_apply, hg, map_add, hfm, hfm]) y
  exact LinearMap.congr_fun (hf.ext (h := h ∘ₗ LinearMap.mulRight T y)
    (h' := LinearMap.mulRight T (h y) + LinearMap.mulRight T y ∘ₗ h) fun a => h1 a y) x

end Jordan

section Add

variable {M : Type*} {N : Type v} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
variable {f : M →ₛₗ[σ] N} (hf : IsSemilinearBaseChange f)

theorem extend_add (g g' : M →ₗ[S] M) : hf.extend (g + g') = hf.extend g + hf.extend g' :=
  hf.ext fun x => by
    rw [LinearMap.add_apply, extend_apply, extend_apply, extend_apply, LinearMap.add_apply,
      map_add]

theorem extend_sub (g g' : M →ₗ[S] M) : hf.extend (g - g') = hf.extend g - hf.extend g' :=
  hf.ext fun x => by
    rw [LinearMap.sub_apply, extend_apply, extend_apply, extend_apply, LinearMap.sub_apply,
      map_sub]

end Add

end IsSemilinearBaseChange
