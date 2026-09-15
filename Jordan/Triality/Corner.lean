import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.LinearCombination
import Jordan.Triality.Basic

/-!
# Trialities and idempotents: reduction to a corner ring

Let `e ∈ R` be a self-adjoint idempotent (`e * e = e`, `star e = e`). The corner ring `eR` (Mathlib's
`IsIdempotentElem.Corner`, with unit `e`) inherits a `star`, and `R → eR`, `r ↦ e r` is a
star-compatible ring hom. Modules on which `e` acts as the identity are the same thing as
`eR`-modules, and this lets a triality be moved between `R` and `eR`:

* `Triality.restrict`: a triality over `R` whose three modules are fixed by `e` is a triality over
  `eR` on the same carriers (`Triality.Restrict`), with the same product read in `eR ⊆ R`.
* `Triality.lift`: a triality over `eR` is a triality over `R` on the same carriers
  (`Triality.Lift`, the `R`-action being through `R → eR`), with the product read in `R`.

The main theorem `Triality.equiv_lift_or_equiv_lift`: every triality over `R` is isomorphic
(`Triality.Equiv`) to the lift of its restriction to `eR`, or to the lift of its restriction to
`(1 - e)R`. In other words `Triality.forall_smul_eq_self_or_forall_one_sub_smul_eq_self` holds for
all three modules simultaneously, with the same idempotent, and the triality is the one over the
corner. The proof is the Peirce argument of `Triality.Basic` applied to each module, plus the
observation that mixed components (`M1 = eM1` but `M2 = (1 - e)M2`, say) force `t = 0`.
-/

universe u v

namespace Triality

variable {R : Type u} [CommRing R] [StarRing R] {e : R} (he : IsIdempotentElem e) (hs : star e = e)

theorem star_one_sub (hs : star e = e) : star (1 - e) = 1 - e := by rw [star_sub, star_one, hs]

section CornerRing

/-! ### The corner ring `eR` with its star -/

/-- The corner ring `eR` (Mathlib's `he.Corner`), as a type keyed on the self-adjoint idempotent
so that it can carry the star inherited from `R`. -/
def Corner (he : IsIdempotentElem e) (_hs : star e = e) : Type u := he.Corner

namespace Corner

instance : CommRing (Corner he hs) := inferInstanceAs (CommRing he.Corner)

theorem mul_val (a : Corner he hs) : e * a.1 = a.1 := ((Subsemigroup.mem_corner_iff he).mp a.2).1
theorem val_mul_e (a : Corner he hs) : a.1 * e = a.1 := ((Subsemigroup.mem_corner_iff he).mp a.2).2

theorem ext {a b : Corner he hs} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- An element of the corner from `r ∈ R` with `e * r = r`. -/
def mk (r : R) (h : e * r = r) : Corner he hs :=
  ⟨r, (Subsemigroup.mem_corner_iff he).mpr ⟨h, by rw [mul_comm]; exact h⟩⟩

@[simp] theorem mk_val (r : R) (h : e * r = r) : (Corner.mk he hs r h).1 = r := rfl
@[simp] theorem val_one : (1 : Corner he hs).1 = e := rfl
@[simp] theorem val_zero : (0 : Corner he hs).1 = 0 := rfl
@[simp] theorem val_mul (a b : Corner he hs) : (a * b).1 = a.1 * b.1 := rfl
@[simp] theorem val_add (a b : Corner he hs) : (a + b).1 = a.1 + b.1 := rfl

instance : StarRing (Corner he hs) where
  star a := Corner.mk he hs (star a.1) (by
    rw [show e * star a.1 = star (a.1 * star e) by rw [star_mul, star_star], hs, val_mul_e])
  star_involutive a := Corner.ext he hs (star_star a.1)
  star_mul a b := Corner.ext he hs (star_mul a.1 b.1)
  star_add a b := Corner.ext he hs (star_add a.1 b.1)

@[simp] theorem val_star (a : Corner he hs) : (star a).1 = star a.1 := rfl

/-- The projection `R →+* eR`, `r ↦ e * r`. -/
def proj : R →+* Corner he hs where
  toFun r := Corner.mk he hs (e * r) (by rw [← mul_assoc, he.eq])
  map_one' := Corner.ext he hs (mul_one e)
  map_mul' r s := Corner.ext he hs (by simp only [mk_val, val_mul]; rw [mul_mul_mul_comm, he.eq])
  map_zero' := Corner.ext he hs (mul_zero e)
  map_add' r s := Corner.ext he hs (mul_add e r s)

@[simp] theorem proj_val (r : R) : (proj he hs r).1 = e * r := rfl

theorem proj_val_self (a : Corner he hs) : proj he hs a.1 = a := Corner.ext he hs (mul_val he hs a)

theorem proj_star (r : R) : proj he hs (star r) = star (proj he hs r) :=
  Corner.ext he hs (by rw [proj_val, val_star, proj_val, star_mul, hs, mul_comm])

end Corner

end CornerRing

section CornerModules

/-! ### Modules over the corner

An `R`-module `M` with a compatible `eR`-module structure (`a • x = (a : R) • x`) is one on which
`e` acts as the identity; such modules are exactly the `eR`-modules, and their `R`-duals and
`eR`-duals coincide. -/

open Corner

/-- Compatibility of an `R`-module structure and an `eR`-module structure on the same type. -/
class IsCornerModule (he : IsIdempotentElem e) (hs : star e = e) (M : Type v) [AddCommGroup M]
    [Module R M] [Module (Corner he hs) M] : Prop where
  corner_smul : ∀ (a : Corner he hs) (x : M), a • x = a.1 • x

variable {M : Type v} [AddCommGroup M] [Module R M] [Module (Corner he hs) M]
  [IsCornerModule he hs M]
include he hs

theorem e_smul (x : M) : e • x = x := by
  have := IsCornerModule.corner_smul (he := he) (hs := hs) (1 : Corner he hs) x
  rw [one_smul] at this
  exact this.symm

theorem smul_eq_proj_smul (r : R) (x : M) : r • x = proj he hs r • x := by
  rw [IsCornerModule.corner_smul, proj_val, mul_smul, e_smul he hs]

theorem e_smul_dual (φ : Module.Dual R M) : e • φ = φ := LinearMap.ext fun z => by
  rw [LinearMap.smul_apply, smul_eq_mul, ← smul_eq_mul, ← map_smul, e_smul he hs]

/-- `R`-functionals and `eR`-functionals on a corner module coincide. -/
def dualEquiv : Module.Dual R M ≃+ Module.Dual (Corner he hs) M where
  toFun φ :=
    { toFun := fun z => Corner.mk he hs (φ z) (by rw [← smul_eq_mul, ← map_smul, e_smul he hs])
      map_add' := fun z z' => Corner.ext he hs (by simp only [mk_val, val_add, map_add])
      map_smul' := fun a z => Corner.ext he hs (by
        simp only [mk_val, RingHom.id_apply, smul_eq_mul, val_mul]
        rw [IsCornerModule.corner_smul, map_smul, smul_eq_mul]) }
  invFun ψ :=
    { toFun := fun z => (ψ z).1
      map_add' := fun z z' => by rw [map_add, val_add]
      map_smul' := fun r z => by
        rw [RingHom.id_apply, smul_eq_mul, smul_eq_proj_smul he hs, map_smul, smul_eq_mul, val_mul,
          proj_val, mul_comm e r, mul_assoc, mul_val] }
  left_inv φ := LinearMap.ext fun _ => rfl
  right_inv ψ := LinearMap.ext fun _ => Corner.ext he hs rfl
  map_add' φ φ' := LinearMap.ext fun _ => Corner.ext he hs rfl

@[simp] theorem dualEquiv_apply_val (φ : Module.Dual R M) (z : M) :
    (dualEquiv he hs φ z).1 = φ z := rfl

@[simp] theorem dualEquiv_symm_apply (ψ : Module.Dual (Corner he hs) M) (z : M) :
    (dualEquiv he hs).symm ψ z = (ψ z).1 := rfl

theorem dualEquiv_smul (a : Corner he hs) (φ : Module.Dual R M) :
    dualEquiv he hs (a.1 • φ) = a • dualEquiv he hs φ :=
  LinearMap.ext fun _ => Corner.ext he hs rfl

theorem dualEquiv_symm_smul (a : Corner he hs) (ψ : Module.Dual (Corner he hs) M) :
    (dualEquiv he hs).symm (a • ψ) = a.1 • (dualEquiv he hs).symm ψ :=
  LinearMap.ext fun _ => rfl

/-- Conjugate-linear functionals on a corner module coincide over `R` and over `eR`. -/
def conjDualEquiv :
    (M →ₛₗ[starRingEnd R] R) ≃+ (M →ₛₗ[starRingEnd (Corner he hs)] Corner he hs) where
  toFun g :=
    { toFun := fun y => Corner.mk he hs (g y) (by
        rw [← hs, ← starRingEnd_apply, ← smul_eq_mul, ← map_smulₛₗ, e_smul he hs])
      map_add' := fun y y' => Corner.ext he hs (by simp only [mk_val, val_add, map_add])
      map_smul' := fun a y => Corner.ext he hs (by
        simp only [mk_val, starRingEnd_apply, smul_eq_mul, val_mul, val_star]
        rw [IsCornerModule.corner_smul, map_smulₛₗ, starRingEnd_apply, smul_eq_mul]) }
  invFun ψ :=
    { toFun := fun y => (ψ y).1
      map_add' := fun y y' => by rw [map_add, val_add]
      map_smul' := fun r y => by
        rw [starRingEnd_apply, smul_eq_mul, smul_eq_proj_smul he hs, map_smulₛₗ, starRingEnd_apply,
          smul_eq_mul, val_mul, val_star, proj_val, star_mul, hs, mul_assoc, mul_val] }
  left_inv g := LinearMap.ext fun _ => rfl
  right_inv ψ := LinearMap.ext fun _ => Corner.ext he hs rfl
  map_add' g g' := LinearMap.ext fun _ => Corner.ext he hs rfl

@[simp] theorem conjDualEquiv_apply_val (g : M →ₛₗ[starRingEnd R] R) (y : M) :
    (conjDualEquiv he hs g y).1 = g y := rfl

@[simp] theorem conjDualEquiv_symm_apply (ψ : M →ₛₗ[starRingEnd (Corner he hs)] Corner he hs)
    (y : M) : (conjDualEquiv he hs).symm ψ y = (ψ y).1 := rfl

end CornerModules

section Synonyms

/-! ### The two type synonyms -/

open Corner

/-- An `R`-module on which `e` acts as the identity, regarded as an `eR`-module. This is
reducible: its `R`-module structure is literally that of `M`; only the `eR`-action is new. -/
abbrev Restrict (_he : IsIdempotentElem e) (_hs : star e = e) {M : Type v} [AddCommGroup M]
    [Module R M] (_h : ∀ x : M, e • x = x) : Type v := M

namespace Restrict

variable {M : Type v} [AddCommGroup M] [Module R M] (h : ∀ x : M, e • x = x)

instance : Module (Corner he hs) (Restrict he hs h) where
  smul a x := a.1 • x
  one_smul x := h x
  mul_smul a b x := mul_smul a.1 b.1 x
  smul_zero a := smul_zero a.1
  smul_add a x y := smul_add a.1 x y
  add_smul a b x := add_smul a.1 b.1 x
  zero_smul x := zero_smul R x

instance : IsCornerModule he hs (Restrict he hs h) := ⟨fun _ _ => rfl⟩

end Restrict

/-- An `eR`-module, regarded as an `R`-module through `R → eR`. -/
def Lift (he : IsIdempotentElem e) (hs : star e = e) (N : Type v) [AddCommGroup N]
    [Module (Corner he hs) N] : Type v := N

namespace Lift

variable (N : Type v) [AddCommGroup N] [Module (Corner he hs) N]

instance : AddCommGroup (Lift he hs N) := inferInstanceAs (AddCommGroup N)
instance : Module (Corner he hs) (Lift he hs N) := inferInstanceAs (Module (Corner he hs) N)
instance : Module R (Lift he hs N) := Module.compHom N (proj he hs)
instance [Nontrivial N] : Nontrivial (Lift he hs N) := ‹Nontrivial N›

instance : IsCornerModule he hs (Lift he hs N) :=
  ⟨fun a x => by
    show a • x = proj he hs a.1 • x
    rw [proj_val_self]⟩

end Lift

end Synonyms

section RestrictLift

/-! ### `restrict` and `lift` -/

open Corner

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module R M1]
  [AddCommGroup M2] [Module R M2]
  [AddCommGroup M3] [Module R M3]
  (T : Triality R M1 M2 M3)
  (h₁ : ∀ x : M1, e • x = x) (h₂ : ∀ y : M2, e • y = y) (h₃ : ∀ z : M3, e • z = z)

/-- A triality over `R` on modules fixed by `e` is a triality over `eR` on the same carriers. -/
abbrev restrict :
    Triality (Corner he hs) (Restrict he hs h₁) (Restrict he hs h₂) (Restrict he hs h₃) where
  triality_prod := LinearMap.mk₂'ₛₗ (RingHom.id _) (starRingEnd _)
    (fun x y => dualEquiv he hs (T.triality_prod x y))
    (fun x x' y => by rw [map_add, LinearMap.add_apply, map_add])
    (fun a x y => by
      rw [RingHom.id_apply, IsCornerModule.corner_smul (he := he) (hs := hs) a x, map_smul,
        LinearMap.smul_apply, dualEquiv_smul])
    (fun x y y' => by rw [map_add, map_add])
    (fun a x y => by
      rw [IsCornerModule.corner_smul (he := he) (hs := hs) a y, map_smulₛₗ, starRingEnd_apply,
        starRingEnd_apply, ← val_star, dualEquiv_smul])
  nontrivial_x := T.nontrivial_x
  nontrivial_y := T.nontrivial_y
  nontrivial_z := T.nontrivial_z
  bij_x_yz x hx :=
    (dualEquiv he hs (M := Restrict he hs h₃)).bijective.comp (T.bij_x_yz x hx)
  bij_x_zy x hx :=
    (conjDualEquiv he hs (M := Restrict he hs h₂)).bijective.comp (T.bij_x_zy x hx)
  bij_y_xz y hy :=
    (dualEquiv he hs (M := Restrict he hs h₃)).bijective.comp (T.bij_y_xz y hy)
  bij_y_zx y hy :=
    (dualEquiv he hs (M := Restrict he hs h₁)).bijective.comp (T.bij_y_zx y hy)
  bij_z_xy z hz :=
    (conjDualEquiv he hs (M := Restrict he hs h₂)).bijective.comp (T.bij_z_xy z hz)
  bij_z_yx z hz :=
    (dualEquiv he hs (M := Restrict he hs h₁)).bijective.comp (T.bij_z_yx z hz)

@[simp] theorem restrict_triality_prod_val (x : M1) (y : M2) (z : M3) :
    ((restrict he hs T h₁ h₂ h₃).triality_prod x y z).1 = T.triality_prod x y z := rfl

variable {N1 N2 N3 : Type v}
  [AddCommGroup N1] [Module (Corner he hs) N1]
  [AddCommGroup N2] [Module (Corner he hs) N2]
  [AddCommGroup N3] [Module (Corner he hs) N3]
  (T₁ : Triality (Corner he hs) N1 N2 N3)

/-- A triality over `eR` is a triality over `R` on the same carriers. -/
abbrev lift : Triality R (Lift he hs N1) (Lift he hs N2) (Lift he hs N3) where
  triality_prod := LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R)
    (fun x y => (dualEquiv he hs (M := Lift he hs N3)).symm (T₁.triality_prod x y))
    -- `Lift` is a `def`, invisible to `rw`'s instance-level matching, hence `erw`
    (fun x x' y => by erw [map_add, LinearMap.add_apply, map_add])
    (fun r x y => by
      show (dualEquiv he hs (M := Lift he hs N3)).symm
          (T₁.triality_prod (proj he hs r • x) y) = r • _
      erw [map_smul, LinearMap.smul_apply, dualEquiv_symm_smul, proj_val, mul_smul,
        e_smul_dual he hs])
    (fun x y y' => by erw [map_add, map_add])
    (fun r x y => by
      show (dualEquiv he hs (M := Lift he hs N3)).symm
          (T₁.triality_prod x (proj he hs r • y)) = starRingEnd R r • _
      erw [map_smulₛₗ, starRingEnd_apply, starRingEnd_apply, dualEquiv_symm_smul, val_star,
        proj_val, star_mul, hs, mul_smul, e_smul_dual he hs])
  nontrivial_x := T₁.nontrivial_x
  nontrivial_y := T₁.nontrivial_y
  nontrivial_z := T₁.nontrivial_z
  bij_x_yz x hx :=
    (dualEquiv he hs (M := Lift he hs N3)).symm.bijective.comp (T₁.bij_x_yz x hx)
  bij_x_zy x hx :=
    (conjDualEquiv he hs (M := Lift he hs N2)).symm.bijective.comp (T₁.bij_x_zy x hx)
  bij_y_xz y hy :=
    (dualEquiv he hs (M := Lift he hs N3)).symm.bijective.comp (T₁.bij_y_xz y hy)
  bij_y_zx y hy :=
    (dualEquiv he hs (M := Lift he hs N1)).symm.bijective.comp (T₁.bij_y_zx y hy)
  bij_z_xy z hz :=
    (conjDualEquiv he hs (M := Lift he hs N2)).symm.bijective.comp (T₁.bij_z_xy z hz)
  bij_z_yx z hz :=
    (dualEquiv he hs (M := Lift he hs N1)).symm.bijective.comp (T₁.bij_z_yx z hz)

@[simp] theorem lift_triality_prod (x : N1) (y : N2) (z : N3) :
    (lift he hs T₁).triality_prod x y z = (T₁.triality_prod x y z).1 := rfl

/-- `T` is isomorphic to the lift of its restriction: the identity maps are `R`-linear because
`r • x = (e r) • x` on a module fixed by `e`. -/
def liftRestrictEquiv : T.Equiv (lift he hs (restrict he hs T h₁ h₂ h₃)) where
  e₁ :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        show r • x = (proj he hs r).1 • x
        rw [proj_val, mul_smul, h₁] }
  e₂ :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r y => by
        show r • y = (proj he hs r).1 • y
        rw [proj_val, mul_smul, h₂] }
  e₃ :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => by
        show r • z = (proj he hs r).1 • z
        rw [proj_val, mul_smul, h₃] }
  map_prod _ _ _ := rfl

end RestrictLift

section Peirce

/-! ### Peirce components of `M2` and `M3`, and the main theorem -/

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module R M1]
  [AddCommGroup M2] [Module R M2]
  [AddCommGroup M3] [Module R M3]
  (T : Triality R M1 M2 M3)

omit hs [StarRing R] in
private theorem eq_zero_of_smul_eq_zero (D : Type*) [AddCommGroup D] [Module R D]
    (h1 : ∀ ψ : D, (1 - e) • ψ = 0) (h2 : ∀ ψ : D, e • ψ = 0) (ψ : D) : ψ = 0 := by
  have := h1 ψ
  rwa [sub_smul, one_smul, h2 ψ, sub_zero] at this

include T he hs

/-- If `e • y ≠ 0` then every functional on `M3` is killed by `1 - e` (uses `star e = e`). -/
theorem dual_smul_one_sub_eq_zero_y {y : M2} (hy : e • y ≠ 0) (φ : Module.Dual R M3) :
    (1 - e) • φ = 0 := by
  obtain ⟨x, hx⟩ := (T.bij_y_xz (e • y) hy).2 φ
  rw [← hx, LinearMap.flip_apply, map_smulₛₗ, starRingEnd_apply, hs, smul_smul, sub_mul, one_mul,
    he.eq, sub_self, zero_smul]

/-- Every `y ∈ M2` is killed by `e` or by `1 - e`. -/
theorem smul_eq_zero_or_one_sub_smul_eq_zero_y (y : M2) : e • y = 0 ∨ (1 - e) • y = 0 := by
  by_contra h
  push Not at h
  have h1 := T.dual_smul_one_sub_eq_zero_y he hs h.1
  have h2 : ∀ φ : Module.Dual R M3, e • φ = 0 := fun φ => by
    have := T.dual_smul_one_sub_eq_zero_y he.one_sub (star_one_sub hs) h.2 φ
    rwa [sub_sub_cancel] at this
  have hφ := eq_zero_of_smul_eq_zero (Module.Dual R M3) h1 h2
  have := T.nontrivial_x
  have := T.nontrivial_y
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : M2)
  obtain ⟨x, hx⟩ := exists_ne (0 : M1)
  exact hx ((T.bij_y_xz y₀ hy₀).1 (by
    rw [LinearMap.flip_apply, LinearMap.flip_apply, hφ (T.triality_prod x y₀),
      hφ (T.triality_prod 0 y₀)]))

omit hs in
/-- If `e • z ≠ 0` then every conjugate-linear functional on `M2` is killed by `1 - e`. -/
theorem conjDual_smul_one_sub_eq_zero_z {z : M3} (hz : e • z ≠ 0)
    (ψ : M2 →ₛₗ[starRingEnd R] R) : (1 - e) • ψ = 0 := by
  obtain ⟨x, hx⟩ := (T.bij_z_xy (e • z) hz).2 ψ
  rw [← hx]
  show (1 - e) • (T.triality_prod x).flip (e • z) = 0
  rw [map_smul, smul_smul, sub_mul, one_mul, he.eq, sub_self, zero_smul]

omit hs in
/-- Every `z ∈ M3` is killed by `e` or by `1 - e`. -/
theorem smul_eq_zero_or_one_sub_smul_eq_zero_z (z : M3) : e • z = 0 ∨ (1 - e) • z = 0 := by
  by_contra h
  push Not at h
  have h1 := T.conjDual_smul_one_sub_eq_zero_z he h.1
  have h2 : ∀ ψ : M2 →ₛₗ[starRingEnd R] R, e • ψ = 0 := fun ψ => by
    have := T.conjDual_smul_one_sub_eq_zero_z he.one_sub h.2 ψ
    rwa [sub_sub_cancel] at this
  have hψ := eq_zero_of_smul_eq_zero (M2 →ₛₗ[starRingEnd R] R) h1 h2
  have := T.nontrivial_x
  have := T.nontrivial_z
  obtain ⟨z₀, hz₀⟩ := exists_ne (0 : M3)
  obtain ⟨x, hx⟩ := exists_ne (0 : M1)
  exact hx ((T.bij_z_xy z₀ hz₀).1 (by
    show (T.triality_prod x).flip z₀ = (T.triality_prod 0).flip z₀
    rw [hψ ((T.triality_prod x).flip z₀), hψ ((T.triality_prod 0).flip z₀)]))

/-- `M1` in the `e`-component and `M2` in the `(1 - e)`-component would force `t = 0`. -/
theorem not_mixed₁₂ (h₁ : ∀ x : M1, e • x = x) (h₂ : ∀ y : M2, (1 - e) • y = y) : False := by
  have := T.nontrivial_x
  have := T.nontrivial_y
  obtain ⟨x, hx⟩ := exists_ne (0 : M1)
  obtain ⟨y, hy⟩ := exists_ne (0 : M2)
  refine hy ((T.bij_x_yz x hx).1 ?_)
  rw [map_zero]
  ext z
  rw [LinearMap.zero_apply, ← h₁ x, ← h₂ y]
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    star_one_sub hs]
  linear_combination (-(T.triality_prod x y z)) * he.eq

omit hs in
/-- `M1` in the `e`-component and `M3` in the `(1 - e)`-component would force `t = 0`. -/
theorem not_mixed₁₃ (h₁ : ∀ x : M1, e • x = x) (h₃ : ∀ z : M3, (1 - e) • z = z) : False := by
  have := T.nontrivial_x
  have := T.nontrivial_y
  obtain ⟨x, hx⟩ := exists_ne (0 : M1)
  obtain ⟨y, hy⟩ := exists_ne (0 : M2)
  refine hy ((T.bij_x_yz x hx).1 ?_)
  rw [map_zero]
  ext z
  rw [LinearMap.zero_apply, ← h₁ x, ← h₃ z]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (-(T.triality_prod x y z)) * he.eq

/-- **Reduction to a corner.** For a self-adjoint idempotent `e`, every triality over `R` is
isomorphic to the lift of its restriction to `eR`, or to the lift of its restriction to
`(1 - e)R`. -/
theorem equiv_lift_or_equiv_lift :
    (∃ (h₁ : ∀ x : M1, e • x = x) (h₂ : ∀ y : M2, e • y = y) (h₃ : ∀ z : M3, e • z = z),
      Nonempty (T.Equiv (lift he hs (restrict he hs T h₁ h₂ h₃)))) ∨
    (∃ (h₁ : ∀ x : M1, (1 - e) • x = x) (h₂ : ∀ y : M2, (1 - e) • y = y)
      (h₃ : ∀ z : M3, (1 - e) • z = z),
      Nonempty (T.Equiv (lift he.one_sub (star_one_sub hs)
        (restrict he.one_sub (star_one_sub hs) T h₁ h₂ h₃)))) := by
  have P1 := T.forall_smul_eq_self_or_forall_one_sub_smul_eq_self he
  have P2 := he.forall_smul_eq_self_or (T.smul_eq_zero_or_one_sub_smul_eq_zero_y he hs)
  have P3 := he.forall_smul_eq_self_or (T.smul_eq_zero_or_one_sub_smul_eq_zero_z he)
  rcases P1 with h₁ | h₁
  · have h₂ := P2.resolve_right (T.not_mixed₁₂ he hs h₁)
    have h₃ := P3.resolve_right (T.not_mixed₁₃ he h₁)
    exact Or.inl ⟨h₁, h₂, h₃, ⟨liftRestrictEquiv he hs T h₁ h₂ h₃⟩⟩
  · have h₂ := P2.resolve_left fun h₂ =>
      T.not_mixed₁₂ he.one_sub (star_one_sub hs) h₁ fun y => by rw [sub_sub_cancel]; exact h₂ y
    have h₃ := P3.resolve_left fun h₃ =>
      T.not_mixed₁₃ he.one_sub h₁ fun z => by rw [sub_sub_cancel]; exact h₃ z
    exact Or.inr ⟨h₁, h₂, h₃, ⟨liftRestrictEquiv he.one_sub (star_one_sub hs) T h₁ h₂ h₃⟩⟩

end Peirce

end Triality
