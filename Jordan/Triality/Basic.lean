import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Ideal.Span

/-- A triality: a trilinear form `t : M1 × M2 × M3 → R`, antilinear in the `M2` slot,
on nontrivial modules, such that for a nonzero element fixed in any one slot the other
two modules are paired perfectly. Nondegeneracy in each slot (`nondegen_xy` etc.)
follows. -/
class Triality (R : outParam (Type u)) (M1 M2 M3 : Type v)
  [CommRing R] [StarRing R]
  [AddCommGroup M1] [Module R M1]
  [AddCommGroup M2] [Module R M2]
  [AddCommGroup M3] [Module R M3] where
  triality_prod : M1 →ₗ[R] M2 →ₛₗ[starRingEnd R] M3 →ₗ[R] R
  nontrivial_x : Nontrivial M1
  nontrivial_y : Nontrivial M2
  nontrivial_z : Nontrivial M3
  /-- Fixing a nonzero element of one module, the pairing of the other two is perfect:
  each is carried isomorphically onto the (conjugate) dual of the other. -/
  bij_x_yz : ∀ x, x ≠ 0 → Function.Bijective (triality_prod x)
  bij_x_zy : ∀ x, x ≠ 0 → Function.Bijective (triality_prod x).flip
  bij_y_xz : ∀ y, y ≠ 0 → Function.Bijective (triality_prod.flip y)
  bij_y_zx : ∀ y, y ≠ 0 → Function.Bijective (triality_prod.flip y).flip
  bij_z_xy : ∀ z, z ≠ 0 → Function.Bijective (fun x => (triality_prod x).flip z)
  bij_z_yx : ∀ z, z ≠ 0 → Function.Bijective (fun y => (triality_prod.flip y).flip z)

namespace Triality

variable {R M1 M2 M3} [CommRing R] [StarRing R]
  [AddCommGroup M1] [Module R M1]
  [AddCommGroup M2] [Module R M2]
  [AddCommGroup M3] [Module R M3]
  (T : Triality R M1 M2 M3)

section Recurry

/-! ## Re-curryings

`triality_prod` takes its arguments in the order `x y z`; the other two orderings that
keep the bar on `M2` (as a `→ₛₗ[starRingEnd R]` domain or a conjugate-dual target). -/

/-- `x z ↦ (y ↦ t x y z)`. -/
public def triality_prod_xz : M1 →ₗ[R] M3 →ₗ[R] (M2 →ₛₗ[starRingEnd R] R) :=
  (LinearMap.lflip : (M2 →ₛₗ[starRingEnd R] M3 →ₗ[R] R) ≃ₗ[R] (M3 →ₗ[R] M2 →ₛₗ[starRingEnd R] R))
    ∘ₗ T.triality_prod

/-- `y z ↦ (x ↦ t x y z)`. -/
public def triality_prod_yz : M2 →ₛₗ[starRingEnd R] M3 →ₗ[R] (M1 →ₗ[R] R) :=
  (LinearMap.lflip : (M1 →ₗ[R] M3 →ₗ[R] R) ≃ₗ[R] (M3 →ₗ[R] M1 →ₗ[R] R)).toLinearMap
    ∘ₛₗ T.triality_prod.flip

variable (x : M1) (y : M2) (z : M3)

@[simp] theorem triality_prod_xz_apply : T.triality_prod_xz x z y = T.triality_prod x y z := rfl
@[simp] theorem triality_prod_yz_apply : T.triality_prod_yz y z x = T.triality_prod x y z := rfl

end Recurry

section Nondegen

/-! ## Nondegeneracy

An element is determined by the pairing it induces on the other two modules. This
follows from the `bij_*` axioms because the modules are nontrivial: to see `x = 0`,
pick `y ≠ 0` and use that `x ↦ t x y ·` is injective. -/

theorem nondegen_xy (x : M1) (h : ∀ y z, T.triality_prod x y z = 0) : x = 0 :=
  have := T.nontrivial_y
  let ⟨y, hy⟩ := exists_ne (0 : M2)
  (T.bij_y_xz y hy).1 (a₂ := 0) (by ext z; simp [h])

theorem nondegen_yz (y : M2) (h : ∀ x z, T.triality_prod x y z = 0) : y = 0 :=
  have := T.nontrivial_x
  let ⟨x, hx⟩ := exists_ne (0 : M1)
  (T.bij_x_yz x hx).1 (a₂ := 0) (by ext z; simp [h])

theorem nondegen_zx (z : M3) (h : ∀ x y, T.triality_prod x y z = 0) : z = 0 :=
  have := T.nontrivial_x
  let ⟨x, hx⟩ := exists_ne (0 : M1)
  (T.bij_x_zy x hx).1 (a₂ := 0) (by ext y; simp [h])

theorem triality_prod_injective : Function.Injective T.triality_prod :=
  (injective_iff_map_eq_zero _).mpr fun x hx => T.nondegen_xy x fun y z => by simp [hx]

theorem triality_prod_flip_injective : Function.Injective T.triality_prod.flip :=
  (injective_iff_map_eq_zero _).mpr fun y hy => T.nondegen_yz y fun x z => by
    simpa using congrArg (fun f => f x z) hy

theorem triality_prod_xz_flip_injective : Function.Injective T.triality_prod_xz.flip :=
  (injective_iff_map_eq_zero _).mpr fun z hz => T.nondegen_zx z fun x y => by
    simpa using congrArg (fun f => f x y) hz

end Nondegen

section Divisibility

/-! ## Values of the triality product are divisible by every non-zero-divisor

Surjectivity of `y ↦ t (a • x) y ·` onto `M3ᵛ` means every functional on `M3` is `a • ψ`; so every
value `t x y z` lies in `aR` for every non-zero-divisor `a`. Over a domain this forces every
nonzero value of `t` to be a unit. (This is why the examples live over fields.) -/

variable {a : R} (ha : a ∈ nonZeroDivisors R)
include T ha

/-- A non-zero-divisor of `R` acts injectively on `M1`: if `a • x = 0` then `a * t x y z = 0` for
all `y, z`, so `t x · · = 0` and `x = 0` by nondegeneracy. -/
theorem smul_ne_zero_of_ne_zero {x : M1} (hx : x ≠ 0) : a • x ≠ 0 := fun h =>
  hx <| T.nondegen_xy x fun y z =>
    (mul_left_mem_nonZeroDivisors_eq_zero_iff ha).mp <| by
      rw [← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.smul_apply, ← map_smul, h, map_zero,
        LinearMap.zero_apply, LinearMap.zero_apply]

/-- Every functional on `M3` is divisible by every non-zero-divisor `a`. -/
theorem exists_dual_eq_smul (φ : Module.Dual R M3) : ∃ ψ : Module.Dual R M3, φ = a • ψ :=
  have := T.nontrivial_x
  let ⟨x, hx⟩ := exists_ne (0 : M1)
  let ⟨y, hy⟩ := (T.bij_x_yz (a • x) (T.smul_ne_zero_of_ne_zero ha hx)).2 φ
  ⟨T.triality_prod x y, by rw [← hy, map_smul, LinearMap.smul_apply]⟩

/-- Every value of the triality product lies in `aR` for every non-zero-divisor `a`. -/
theorem triality_prod_mem_span (x : M1) (y : M2) (z : M3) :
    T.triality_prod x y z ∈ Ideal.span {a} := by
  obtain ⟨ψ, hψ⟩ := T.exists_dual_eq_smul ha (T.triality_prod x y)
  rw [hψ, LinearMap.smul_apply, smul_eq_mul]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right a _)

omit ha in
/-- Over a domain, every nonzero value of the triality product is a unit: `u ∈ u²R` gives
`u = u² r`, hence `u r = 1`. -/
theorem eq_zero_or_isUnit [IsDomain R] (x : M1) (y : M2) (z : M3) :
    T.triality_prod x y z = 0 ∨ IsUnit (T.triality_prod x y z) := by
  set u := T.triality_prod x y z with hu_def
  by_cases hu : u = 0
  · exact Or.inl hu
  · right
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp
      (T.triality_prod_mem_span (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hu hu)) x y z)
    have h1 : u * r = 1 := (mul_left_cancel₀ hu (by rw [mul_one, ← mul_assoc, ← hr])).symm
    exact isUnit_iff_exists.mpr ⟨r, h1, by rw [mul_comm]; exact h1⟩

end Divisibility

section Idempotents

/-! ## Reduction along idempotents

An idempotent `e ∈ R` splits `R = eR × (1 - e)R` and each module into its Peirce components
`M = eM ⊕ (1 - e)M`. A triality never mixes the two: every `x ∈ M1` is killed by `e` or by `1 - e`,
and in fact all of `M1` is killed by one of them, so `M1 = eM1` is a module over `eR = eRe` (or
`M1 = (1 - e)M1` over `(1 - e)R`) and the triality reduces to one over that corner. In particular
a triality over a product `R₁ × R₂` (take `e = (1, 0)`) is a triality over one factor.

The reason is the `x ≠ 0` in `bij_x_yz`: if `e • x ≠ 0`, every functional on `M3` is
`t (e • x) y ·`, hence killed by `1 - e`; if also `(1 - e) • x ≠ 0`, every functional is killed by
`e` too, so `M3ᵛ = 0`, contradicting `M2 ≃ M3ᵛ` with `M2` nontrivial.

So after reducing along idempotents one is in a ring with no proper idempotents, and there
`eq_zero_or_isUnit` still needs `IsDomain`: over `F[ε]/(ε²)` the `F`-vector space `F` (with `ε`
acting as `0`) and `t x y z = ε x y z` is a triality whose nonzero values are the nilpotent `ε`. -/

variable {e : R} (he : IsIdempotentElem e)
include T he

/-- If `e • x ≠ 0` then every functional on `M3` is killed by `1 - e`. -/
theorem dual_smul_one_sub_eq_zero {x : M1} (hx : e • x ≠ 0) (φ : Module.Dual R M3) :
    (1 - e) • φ = 0 := by
  obtain ⟨y, hy⟩ := (T.bij_x_yz (e • x) hx).2 φ
  rw [← hy, map_smul, LinearMap.smul_apply, smul_smul, sub_mul, one_mul, he.eq, sub_self,
    zero_smul]

/-- Every `x ∈ M1` is killed by `e` or by `1 - e`. -/
theorem smul_eq_zero_or_one_sub_smul_eq_zero (x : M1) : e • x = 0 ∨ (1 - e) • x = 0 := by
  by_contra h
  push Not at h
  have h1 : ∀ φ : Module.Dual R M3, (1 - e) • φ = 0 := T.dual_smul_one_sub_eq_zero he h.1
  have h2 : ∀ φ : Module.Dual R M3, e • φ = 0 := fun φ => by
    have := T.dual_smul_one_sub_eq_zero he.one_sub h.2 φ
    rwa [sub_sub_cancel] at this
  have hφ : ∀ φ : Module.Dual R M3, φ = 0 := fun φ => LinearMap.ext fun z => by
    have h1z := congrArg (fun ψ : Module.Dual R M3 => ψ z) (h1 φ)
    have h2z := congrArg (fun ψ : Module.Dual R M3 => ψ z) (h2 φ)
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, sub_mul, one_mul] at h1z h2z
    rwa [h2z, sub_zero] at h1z
  have := T.nontrivial_x
  have := T.nontrivial_y
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : M1)
  obtain ⟨y, hy⟩ := exists_ne (0 : M2)
  exact hy ((T.bij_x_yz x₀ hx₀).1 (by rw [hφ (T.triality_prod x₀ y), hφ (T.triality_prod x₀ 0)]))

omit T [StarRing R] in
/-- Module-theoretic half of the Peirce argument: if every element of `M` is killed by `e` or by
`1 - e`, then all of `M` is fixed by `e` or all of it by `1 - e`. -/
theorem _root_.IsIdempotentElem.forall_smul_eq_self_or {M : Type*} [AddCommGroup M] [Module R M]
    (H : ∀ x : M, e • x = 0 ∨ (1 - e) • x = 0) :
    (∀ x : M, e • x = x) ∨ (∀ x : M, (1 - e) • x = x) := by
  have key : (∀ x : M, e • x = 0) ∨ (∀ x : M, (1 - e) • x = 0) := by
    by_contra h
    push Not at h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    rcases H (e • a + (1 - e) • b) with h' | h'
    · apply ha
      rwa [smul_add, smul_smul, he.eq, smul_smul, mul_sub, mul_one, he.eq, sub_self, zero_smul,
        add_zero] at h'
    · apply hb
      rwa [smul_add, smul_smul, sub_mul, one_mul, he.eq, sub_self, zero_smul, zero_add, smul_smul,
        he.one_sub.eq] at h'
  -- killed by `1 - e` means fixed by `e`, and vice versa
  exact key.symm.imp
    (fun h x => by have := h x; rwa [sub_smul, one_smul, sub_eq_zero, eq_comm] at this)
    (fun h x => by rw [sub_smul, one_smul, h x, sub_zero])

/-- `M1` is a single Peirce component: `M1 = eM1` (every `x` is `e • x`, so `R` acts through the
corner `eR = eRe` and the triality is one over `eR`), or likewise for `1 - e`. -/
theorem forall_smul_eq_self_or_forall_one_sub_smul_eq_self :
    (∀ x : M1, e • x = x) ∨ (∀ x : M1, (1 - e) • x = x) :=
  he.forall_smul_eq_self_or (T.smul_eq_zero_or_one_sub_smul_eq_zero he)

end Idempotents

section Equiv

/-! ## Isomorphisms of trialities -/

variable {N1 N2 N3 : Type v}
  [AddCommGroup N1] [Module R N1]
  [AddCommGroup N2] [Module R N2]
  [AddCommGroup N3] [Module R N3]

/-- An isomorphism of trialities over the same ring: linear isomorphisms of the three modules
carrying one triality product to the other. -/
structure Equiv (T : Triality R M1 M2 M3) (T' : Triality R N1 N2 N3) where
  e₁ : M1 ≃ₗ[R] N1
  e₂ : M2 ≃ₗ[R] N2
  e₃ : M3 ≃ₗ[R] N3
  map_prod : ∀ x y z, T'.triality_prod (e₁ x) (e₂ y) (e₃ z) = T.triality_prod x y z

end Equiv

section Duals

/-! ## Duality isomorphisms

Fixing a nonzero element of one of the three modules, the triality product identifies
each of the other two with the dual of the remaining one. The bar sits wherever `M2`
does: as a domain it is a `≃ₛₗ[starRingEnd R]`, as a target it is the conjugate dual
`M2 →ₛₗ[starRingEnd R] R`. -/

variable (x : M1) (y : M2) (z : M3)

/-- Nonzero `x ∈ M1`: antilinear isomorphism `M2 ≃ M3ᵛ`, `y ↦ (z ↦ t x y z)`. -/
public noncomputable def xEquiv₂₃ (hx : x ≠ 0) : M2 ≃ₛₗ[starRingEnd R] Module.Dual R M3 :=
  LinearEquiv.ofBijective (T.triality_prod x) (T.bij_x_yz x hx)

/-- Nonzero `x ∈ M1`: linear isomorphism `M3 ≃ M̄2ᵛ`, `z ↦ (y ↦ t x y z)`. -/
public noncomputable def xEquiv₃₂ (hx : x ≠ 0) : M3 ≃ₗ[R] (M2 →ₛₗ[starRingEnd R] R) :=
  LinearEquiv.ofBijective (T.triality_prod_xz x) (T.bij_x_zy x hx)

/-- Nonzero `y ∈ M2`: linear isomorphism `M1 ≃ M3ᵛ`, `x ↦ (z ↦ t x y z)`. -/
public noncomputable def yEquiv₁₃ (hy : y ≠ 0) : M1 ≃ₗ[R] Module.Dual R M3 :=
  LinearEquiv.ofBijective (T.triality_prod.flip y) (T.bij_y_xz y hy)

/-- Nonzero `y ∈ M2`: linear isomorphism `M3 ≃ M1ᵛ`, `z ↦ (x ↦ t x y z)`. -/
public noncomputable def yEquiv₃₁ (hy : y ≠ 0) : M3 ≃ₗ[R] Module.Dual R M1 :=
  LinearEquiv.ofBijective (T.triality_prod_yz y) (T.bij_y_zx y hy)

/-- Nonzero `z ∈ M3`: linear isomorphism `M1 ≃ M̄2ᵛ`, `x ↦ (y ↦ t x y z)`. -/
public noncomputable def zEquiv₁₂ (hz : z ≠ 0) : M1 ≃ₗ[R] (M2 →ₛₗ[starRingEnd R] R) :=
  LinearEquiv.ofBijective (T.triality_prod_xz.flip z) (T.bij_z_xy z hz)

/-- Nonzero `z ∈ M3`: antilinear isomorphism `M2 ≃ M1ᵛ`, `y ↦ (x ↦ t x y z)`. -/
public noncomputable def zEquiv₂₁ (hz : z ≠ 0) : M2 ≃ₛₗ[starRingEnd R] Module.Dual R M1 :=
  LinearEquiv.ofBijective (T.triality_prod_yz.flip z) (T.bij_z_yx z hz)

@[simp] theorem xEquiv₂₃_apply (hx) : T.xEquiv₂₃ x hx y z = T.triality_prod x y z := rfl
@[simp] theorem xEquiv₃₂_apply (hx) : T.xEquiv₃₂ x hx z y = T.triality_prod x y z := rfl
@[simp] theorem yEquiv₁₃_apply (hy) : T.yEquiv₁₃ y hy x z = T.triality_prod x y z := rfl
@[simp] theorem yEquiv₃₁_apply (hy) : T.yEquiv₃₁ y hy z x = T.triality_prod x y z := rfl
@[simp] theorem zEquiv₁₂_apply (hz) : T.zEquiv₁₂ z hz x y = T.triality_prod x y z := rfl
@[simp] theorem zEquiv₂₁_apply (hz) : T.zEquiv₂₁ z hz y x = T.triality_prod x y z := rfl

end Duals

section OfTrivialStar

/-! ## Trialities from trilinear forms when `star` is trivial

When `star = id` on `R`, a `starRingEnd R`-semilinear map is the same thing as a linear map, so an
ordinary trilinear form `M1 →ₗ M2 →ₗ M3 →ₗ R` gives a `Triality`, with the perfect-pairing axioms
stated for the plain form. -/

variable [TrivialStar R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- With trivial `star`, linear and `starRingEnd R`-semilinear maps coincide. -/
def linearEquivStarSemilinear : (M →ₗ[R] N) ≃ₗ[R] (M →ₛₗ[starRingEnd R] N) where
  toFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r m => by rw [map_smul, starRingEnd_apply, star_trivial] }
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r m => by rw [map_smulₛₗ, starRingEnd_apply, star_trivial]; rfl }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem linearEquivStarSemilinear_apply (f : M →ₗ[R] N) (m : M) :
    linearEquivStarSemilinear f m = f m := rfl

variable (t : M1 →ₗ[R] M2 →ₗ[R] M3 →ₗ[R] R)

/-- A triality from an ordinary trilinear form, when `star` on `R` is trivial. -/
abbrev ofTrivialStar [Nontrivial M1] [Nontrivial M2] [Nontrivial M3]
    (bij_x_yz : ∀ x, x ≠ 0 → Function.Bijective (t x))
    (bij_x_zy : ∀ x, x ≠ 0 → Function.Bijective (t x).flip)
    (bij_y_xz : ∀ y, y ≠ 0 → Function.Bijective (t.flip y))
    (bij_y_zx : ∀ y, y ≠ 0 → Function.Bijective (t.flip y).flip)
    (bij_z_xy : ∀ z, z ≠ 0 → Function.Bijective (fun x => (t x).flip z))
    (bij_z_yx : ∀ z, z ≠ 0 → Function.Bijective (fun y => (t.flip y).flip z)) :
    Triality R M1 M2 M3 where
  triality_prod := linearEquivStarSemilinear.toLinearMap ∘ₗ t
  nontrivial_x := inferInstance
  nontrivial_y := inferInstance
  nontrivial_z := inferInstance
  bij_x_yz := bij_x_yz
  bij_x_zy x hx := linearEquivStarSemilinear.bijective.comp (bij_x_zy x hx)
  bij_y_xz := bij_y_xz
  bij_y_zx := bij_y_zx
  bij_z_xy z hz := linearEquivStarSemilinear.bijective.comp (bij_z_xy z hz)
  bij_z_yx := bij_z_yx

@[simp] theorem ofTrivialStar_triality_prod [Nontrivial M1] [Nontrivial M2] [Nontrivial M3]
    (h₁ h₂ h₃ h₄ h₅ h₆) (x : M1) (y : M2) (z : M3) :
    (ofTrivialStar t h₁ h₂ h₃ h₄ h₅ h₆).triality_prod x y z = t x y z := rfl

end OfTrivialStar

end Triality
