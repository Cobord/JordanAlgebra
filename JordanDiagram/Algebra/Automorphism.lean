module

public import Jordan.StructureAlgebra
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Jordan automorphisms, stabilizers, and lifting along injective homomorphisms

Morphisms of `Jord_R` (Definition 2.3 of the paper) are `R`-linear maps preserving the Jordan
product, with no unit condition; in Mathlib these are the non-unital algebra homomorphisms
`A →ₙₐ[R] B`. Mathlib has no group structure on bijective such maps, so the automorphism group
`Aut_{Jord_R}(A)` is taken to be `jordanAut R A`, the subgroup of the linear automorphism group
`A ≃ₗ[R] A` cut out by multiplicativity.

The main technical tool for terminal determination (Propositions 3.6 and 3.8) is lifting along an
injective homomorphism `ν : A →ₙₐ[R] J`: an automorphism `h` of `J` preserving `range ν` setwise
transports to a unique automorphism `g` of `A` with `ν ∘ g = h ∘ ν` (`liftAut`), and a derivation
of `J` preserving `range ν` transports to a derivation of `A` (`liftDer`).
-/

@[expose] public section

open scoped Pointwise

/-- For a bijection `f`, `f '' S = S` exactly when `f x ∈ S ↔ x ∈ S` for every `x`. -/
theorem Function.Bijective.image_eq_self_iff {X : Type*} {f : X → X}
    (hf : Function.Bijective f) {S : Set X} : f '' S = S ↔ ∀ x, f x ∈ S ↔ x ∈ S := by
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [← hf.1 hyx]
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).2 hx
    · intro hy
      obtain ⟨x, rfl⟩ := hf.2 y
      exact ⟨x, (h x).1 hy, rfl⟩

namespace JordanAlgebra

variable (R : Type*) [CommRing R]

section Aut

variable (A : Type*) [JordanAlgebra R A]

/-- The Jordan automorphism group `Aut_{Jord_R}(A)`: linear automorphisms preserving the product. -/
def jordanAut : Subgroup (A ≃ₗ[R] A) where
  carrier := {g | ∀ x y, g (x * y) = g x * g y}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x y := by
    change g (h (x * y)) = g (h x) * g (h y)
    rw [hh, hg]
  inv_mem' {g} hg x y := by
    change g.symm (x * y) = g.symm x * g.symm y
    apply g.injective
    rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

variable {R A}

theorem mem_jordanAut {g : A ≃ₗ[R] A} : g ∈ jordanAut R A ↔ ∀ x y, g (x * y) = g x * g y :=
  Iff.rfl

namespace jordanAut

instance : CoeFun (jordanAut R A) (fun _ => A → A) := ⟨fun g => ((g : A ≃ₗ[R] A) : A → A)⟩

@[simp]
theorem coe_mk (g : A ≃ₗ[R] A) (hg) : ((⟨g, hg⟩ : jordanAut R A) : A → A) = g := rfl

theorem map_mul (g : jordanAut R A) (x y : A) : g (x * y) = g x * g y := g.2 x y

@[simp]
theorem one_apply (x : A) : (1 : jordanAut R A) x = x := rfl

@[simp]
theorem mul_apply (g h : jordanAut R A) (x : A) : (g * h) x = g (h x) := rfl

@[simp]
theorem inv_apply_self (g : jordanAut R A) (x : A) : g⁻¹ (g x) = x :=
  (g : A ≃ₗ[R] A).symm_apply_apply x

@[simp]
theorem apply_inv_self (g : jordanAut R A) (x : A) : g (g⁻¹ x) = x :=
  (g : A ≃ₗ[R] A).apply_symm_apply x

theorem injective (g : jordanAut R A) : Function.Injective g :=
  (g : A ≃ₗ[R] A).injective

@[ext]
theorem ext {g h : jordanAut R A} (H : ∀ x, g x = h x) : g = h :=
  Subtype.ext (LinearEquiv.ext H)

/-- A Jordan automorphism as a morphism of `Jord_R`. -/
def toHom (g : jordanAut R A) : A →ₙₐ[R] A where
  toFun := g
  map_smul' := (g : A ≃ₗ[R] A).map_smul
  map_zero' := (g : A ≃ₗ[R] A).map_zero
  map_add' := (g : A ≃ₗ[R] A).map_add
  map_mul' := jordanAut.map_mul g

@[simp]
theorem toHom_apply (g : jordanAut R A) (x : A) : toHom g x = g x := rfl

/-- The setwise stabilizer `Stab(S) = {h : h(S) = S}` of a subset `S` of `A`. -/
def stab (S : Set A) : Subgroup (jordanAut R A) :=
  (MulAction.stabilizer (A ≃ₗ[R] A) S).comap (jordanAut R A).subtype

theorem mem_stab {S : Set A} {h : jordanAut R A} : h ∈ stab S ↔ h '' S = S := by
  change (h : A ≃ₗ[R] A) • S = S ↔ _
  rw [← Set.image_smul]
  rfl

theorem image_eq_self_iff (h : jordanAut R A) {S : Set A} :
    h '' S = S ↔ ∀ x, h x ∈ S ↔ x ∈ S :=
  (h : A ≃ₗ[R] A).bijective.image_eq_self_iff

end jordanAut

end Aut

section Lift

variable {R} {A J : Type*} [JordanAlgebra R A] [JordanAlgebra R J]
variable {ν : A →ₙₐ[R] J}

/-- The underlying linear map of a morphism of `Jord_R`. -/
def toLin (ν : A →ₙₐ[R] J) : A →ₗ[R] J where
  toFun := ν
  map_add' := map_add ν
  map_smul' := map_smul ν

@[simp]
theorem toLin_apply (ν : A →ₙₐ[R] J) (x : A) : toLin ν x = ν x := rfl

/-- `range ν` as a submodule. -/
abbrev rangeSubmodule (ν : A →ₙₐ[R] J) : Submodule R J := LinearMap.range (toLin ν)

theorem coe_rangeSubmodule (ν : A →ₙₐ[R] J) : (rangeSubmodule ν : Set J) = Set.range ν :=
  LinearMap.coe_range _

/-- The identification of `A` with `range ν` for injective `ν`. -/
noncomputable def rangeEquiv (hν : Function.Injective ν) : A ≃ₗ[R] rangeSubmodule ν :=
  LinearEquiv.ofInjective (toLin ν) hν

theorem rangeEquiv_symm_spec (hν : Function.Injective ν) (y : rangeSubmodule ν) :
    ν ((rangeEquiv hν).symm y) = y := by
  have h := LinearEquiv.ofInjective_apply (toLin ν) (h := hν) ((rangeEquiv hν).symm y)
  change (((rangeEquiv hν) ((rangeEquiv hν).symm y) : rangeSubmodule ν) : J) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The linear automorphism of `A` transported from `h` along an injective `ν`. -/
noncomputable def liftEquiv (hν : Function.Injective ν) (h : J ≃ₗ[R] J)
    (hS : h '' Set.range ν = Set.range ν) : A ≃ₗ[R] A :=
  (rangeEquiv hν).trans <|
    (h.ofSubmodules (rangeSubmodule ν) (rangeSubmodule ν) (by
      apply SetLike.coe_injective
      rw [Submodule.map_coe, coe_rangeSubmodule]
      exact hS)).trans (rangeEquiv hν).symm

theorem liftEquiv_spec (hν : Function.Injective ν) (h : J ≃ₗ[R] J)
    (hS : h '' Set.range ν = Set.range ν) (x : A) : ν (liftEquiv hν h hS x) = h (ν x) := by
  change ν ((rangeEquiv hν).symm _) = _
  rw [rangeEquiv_symm_spec]
  rfl

/-- Lifting an automorphism `h` of `J` that preserves `range ν` along an injective `ν`. -/
noncomputable def liftAut (hν : Function.Injective ν) (h : jordanAut R J)
    (hS : h '' Set.range ν = Set.range ν) : jordanAut R A :=
  ⟨liftEquiv hν h hS, by
    intro x y
    apply hν
    rw [liftEquiv_spec, map_mul ν x y, map_mul ν, liftEquiv_spec, liftEquiv_spec]
    exact jordanAut.map_mul h _ _⟩

theorem liftAut_spec (hν : Function.Injective ν) (h : jordanAut R J)
    (hS : h '' Set.range ν = Set.range ν) (x : A) : ν (liftAut hν h hS x) = h (ν x) :=
  liftEquiv_spec hν h hS x

/-- Lifting a derivation of `J` that maps `range ν` into itself along an injective `ν`. -/
noncomputable def liftDer (hν : Function.Injective ν) (d : JordanDerivation R J)
    (hS : ∀ x, d (ν x) ∈ Set.range ν) : JordanDerivation R A where
  toLinearMap := (rangeEquiv hν).symm.toLinearMap ∘ₗ
      ((d : J →ₗ[R] J).restrict (p := rangeSubmodule ν) (q := rangeSubmodule ν) (by
        rintro _ ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := hS x
        exact ⟨y, hy⟩)) ∘ₗ (rangeEquiv hν).toLinearMap
  leibniz' a b := by
    have spec : ∀ x, ν ((rangeEquiv hν).symm ((d : J →ₗ[R] J).restrict
        (p := rangeSubmodule ν) (q := rangeSubmodule ν) (by
          rintro _ ⟨x, rfl⟩
          obtain ⟨y, hy⟩ := hS x
          exact ⟨y, hy⟩) (rangeEquiv hν x))) = d (ν x) := fun x => by
      rw [rangeEquiv_symm_spec]
      rfl
    apply hν
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [spec, map_mul ν a b, map_add ν, map_mul ν a, map_mul ν _ b, spec, spec,
      JordanDerivation.leibniz]

theorem liftDer_spec (hν : Function.Injective ν) (d : JordanDerivation R J)
    (hS : ∀ x, d (ν x) ∈ Set.range ν) (x : A) : ν (liftDer hν d hS x) = d (ν x) := by
  change ν ((rangeEquiv hν).symm _) = _
  rw [rangeEquiv_symm_spec]
  rfl

end Lift

end JordanAlgebra
