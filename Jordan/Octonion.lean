import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Unique
import Jordan.RealQM
import Jordan.SpinFactor

/-!
# Generalized octonion algebras

The generalized octonion algebra `Octonion R a b c`, for a commutative ring `R` with `2`
invertible and `a b c : R`, is the `8`-dimensional `R`-algebra obtained by one further step of
Cayley-Dickson doubling applied to the quaternion algebra `ℍ[R, a, 0, b]`, by the parameter `c`.

This is the fully general `3`-parameter family: each of `a`, `b`, `c` is one independent
Cayley-Dickson doubling step (`R → R[i] → ℍ → 𝕆`), and Hamilton/Cayley's octonions are just the
specialization `R = ℝ`, `a = b = c = -1`. There is no loss of generality in building the
intermediate quaternion stage as `ℍ[R, a, 0, b]` (no `c₂` deformation term) rather than the fully
general `ℍ[R, a, c₂, b]`: with `2` invertible we can always "complete the square" to eliminate
that term, so `ℍ[R, a, 0, b]` already realizes every quaternion algebra in this family up to
isomorphism (as in `QuaternionicQM`/`ComplexQM`).

`Octonion R a b c` is a *non-associative* unital `R`-algebra: we do not (and cannot) claim
`Ring`/associativity here. What it *does* satisfy is the alternative laws
`x * (x * y) = (x * x) * y` and `(y * x) * x = y * (x * x)` -- the hallmark weaker substitute for
associativity that makes octonion algebras well-behaved (e.g. it is what eventually lets the `3x3`
Hermitian-matrix Albert algebra construction work, unlike for a generic non-associative algebra).
-/

open scoped Quaternion

/-- An *alternative* magma: multiplication need not be associative, but it satisfies the two
weaker laws that survive Cayley-Dickson doubling of an associative algebra (such as the
octonions, doubled from the associative quaternions). Mathlib has no class for this notion yet. -/
class IsAlternative (M : Type*) [Mul M] : Prop where
  /-- The left alternative law: `x * (x * y) = (x * x) * y`. -/
  mul_alternative_left : ∀ x y : M, x * (x * y) = (x * x) * y
  /-- The right alternative law: `(y * x) * x = y * (x * x)`. -/
  mul_alternative_right : ∀ x y : M, (y * x) * x = y * (x * x)

/-- The generalized octonion algebra `O(a, b, c)` over `R`: one further step of Cayley-Dickson
doubling applied to the quaternion algebra `ℍ[R, a, 0, b]`, by the parameter `c`. A type synonym
for `ℍ[R,a,0,b] × ℍ[R,a,0,b]`, kept distinct so the `c`-dependent `Mul`/`Star` instances below
don't clash with instances belonging to a different choice of `c`. -/
def Octonion (R : Type*) [CommRing R] (a b _c : R) : Type _ := ℍ[R, a, 0, b] × ℍ[R, a, 0, b]

namespace Octonion

variable {R : Type*} [CommRing R] {a b c : R}

instance : AddCommGroup (Octonion R a b c) :=
  (inferInstance : AddCommGroup (ℍ[R, a, 0, b] × ℍ[R, a, 0, b]))

instance : Module R (Octonion R a b c) :=
  (inferInstance : Module R (ℍ[R, a, 0, b] × ℍ[R, a, 0, b]))

@[ext] theorem ext {x y : Octonion R a b c} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  Prod.ext h1 h2

@[simp] theorem add_fst (x y : Octonion R a b c) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem add_snd (x y : Octonion R a b c) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem zero_fst : (0 : Octonion R a b c).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : Octonion R a b c).2 = 0 := rfl
@[simp] theorem neg_fst (x : Octonion R a b c) : (-x).1 = -x.1 := rfl
@[simp] theorem neg_snd (x : Octonion R a b c) : (-x).2 = -x.2 := rfl
@[simp] theorem smul_fst (r : R) (x : Octonion R a b c) : (r • x).1 = r • x.1 := rfl
@[simp] theorem smul_snd (r : R) (x : Octonion R a b c) : (r • x).2 = r • x.2 := rfl

/-- Build an octonion from its two quaternion components. -/
def mk (p q : ℍ[R, a, 0, b]) : Octonion R a b c := (p, q)

@[simp] theorem mk_fst (p q : ℍ[R, a, 0, b]) : (mk p q : Octonion R a b c).1 = p := rfl
@[simp] theorem mk_snd (p q : ℍ[R, a, 0, b]) : (mk p q : Octonion R a b c).2 = q := rfl

section StarAspects

/- `[StarRing R] [TrivialStar R]` are opened up manifestly starting here, right above `Mul`,
because Cayley-Dickson multiplication is itself *defined* using `star` (of the quaternion
components). As in `QuaternionicQM` (see the module doc there): that `star` -- and hence
`Octonion`'s own `star` below -- is defined purely from `R`'s ring operations and never looks at
any `Star R` instance, so none of `Mul`, `IsScalarTower`, `SMulCommClass`, `Star`, `StarRing`
below actually need these hypotheses. `StarModule` further down is the one declaration where a
*second*, genuinely `R`-level star aspect enters (`star (r • x) = star r • star x` only matches
this `star` when `star r = r`). Keeping `[StarRing R] [TrivialStar R]` visible for this whole
section, rather than opening it only locally right before `StarModule`, makes plain from the very
first `star`-touching declaration that this territory is being entered, instead of leaving it an
easy-to-miss detail of one declaration in the middle. -/
variable [StarRing R] [TrivialStar R]

set_option linter.unusedSectionVars false in
/-- Cayley-Dickson multiplication:
`(p, q) * (r, s) = (p * r - c • (star s * q), s * p + q * star r)`. -/
instance : Mul (Octonion R a b c) where
  mul x y := mk (x.1 * y.1 - c • (star y.2 * x.2)) (y.2 * x.1 + x.2 * star y.1)

set_option linter.unusedSectionVars false in
@[simp] theorem mul_fst (x y : Octonion R a b c) :
    (x * y).1 = x.1 * y.1 - c • (star y.2 * x.2) := rfl
set_option linter.unusedSectionVars false in
@[simp] theorem mul_snd (x y : Octonion R a b c) :
    (x * y).2 = y.2 * x.1 + x.2 * star y.1 := rfl

set_option linter.unusedSectionVars false in
/-- `R`-scaling associates with Cayley-Dickson multiplication on the left: `(r • x) * y = r •
(x * y)`. -/
instance : IsScalarTower R (Octonion R a b c) (Octonion R a b c) where
  smul_assoc r x y := by
    apply Octonion.ext
    · simp only [smul_eq_mul, smul_fst, mul_fst, smul_snd]
      rw [smul_mul_assoc, mul_smul_comm, smul_comm c r, ← smul_sub]
    · simp only [smul_eq_mul, smul_snd, mul_snd, smul_fst]
      rw [mul_smul_comm, smul_mul_assoc, ← smul_add]

set_option linter.unusedSectionVars false in
/-- `R`-scaling commutes across Cayley-Dickson multiplication: `r • (x * y) = x * (r • y)`. The
`star` in the proof is `QuaternionAlgebra`'s own conjugation (via `star_smul'`). -/
instance : SMulCommClass R (Octonion R a b c) (Octonion R a b c) where
  smul_comm r x y := by
    apply Octonion.ext
    · simp only [smul_eq_mul, mul_fst, smul_fst, smul_snd]
      rw [mul_smul_comm, QuaternionAlgebra.star_smul', smul_mul_assoc, smul_comm c r, ← smul_sub]
    · simp only [smul_eq_mul, mul_snd, smul_snd, smul_fst]
      rw [smul_mul_assoc, QuaternionAlgebra.star_smul', mul_smul_comm, ← smul_add]

set_option linter.unusedSectionVars false in
instance : One (Octonion R a b c) := ⟨mk 1 0⟩

set_option linter.unusedSectionVars false in
@[simp] theorem one_fst : (1 : Octonion R a b c).1 = 1 := rfl
set_option linter.unusedSectionVars false in
@[simp] theorem one_snd : (1 : Octonion R a b c).2 = 0 := rfl

set_option linter.unusedSectionVars false in
instance : NonAssocRing (Octonion R a b c) where
  left_distrib x y z := by ext <;> simp [mul_add] <;> ring
  right_distrib x y z := by ext <;> simp [add_mul] <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

set_option linter.unusedSectionVars false in
/-- Cayley-Dickson conjugation: `star (p, q) = (star p, -q)`. -/
instance : Star (Octonion R a b c) where
  star x := mk (star x.1) (-x.2)

set_option linter.unusedSectionVars false in
@[simp] theorem star_fst (x : Octonion R a b c) : (star x).1 = star x.1 := rfl
set_option linter.unusedSectionVars false in
@[simp] theorem star_snd (x : Octonion R a b c) : (star x).2 = -x.2 := rfl

set_option linter.unusedSectionVars false in
/-- Cayley-Dickson conjugation is an involutive anti-automorphism, exactly as for `ℍ` (it never
needs `2` invertible): `star (x * y) = star y * star x`. -/
instance : StarRing (Octonion R a b c) where
  star_involutive x := by apply Octonion.ext <;> simp
  star_add x y := by apply Octonion.ext <;> simp [add_comm]
  star_mul x y := by apply Octonion.ext <;> simp

/-- Octonions form a `StarModule` over `R`: `star` commutes with `R`-scaling, i.e.
`star (r • x) = star r • star x`. This genuinely needs `[StarRing R] [TrivialStar R]` (not just
`[Star R]`): the proof reduces to `r • z = star r • z`, which only holds because `TrivialStar R`
gives `star r = r`. -/
instance : StarModule R (Octonion R a b c) where
  star_smul r x := by
    apply Octonion.ext
    · simp [star_trivial]
    · simp [star_trivial]

omit [StarRing R] [TrivialStar R] in
/-- The trace `p + star p` of a quaternion is a central scalar. -/
private theorem add_star_eq_coe (p : ℍ[R, a, 0, b]) : p + star p = ((2 * p.re : R) : ℍ[R, a, 0, b]) := by
  simpa using QuaternionAlgebra.self_add_star (c₂ := (0 : R)) p

omit [StarRing R] [TrivialStar R] in
private theorem add_star_mul_comm (p q : ℍ[R, a, 0, b]) : (p + star p) * q = q * (p + star p) := by
  rw [add_star_eq_coe]; exact QuaternionAlgebra.coe_commutes _ q

omit [StarRing R] [TrivialStar R] in
/-- The norm `star q * q` of a quaternion is a central scalar, and agrees with `q * star q`. -/
private theorem star_mul_self_eq_coe (q : ℍ[R, a, 0, b]) :
    star q * q = ((star q * q).re : R) := QuaternionAlgebra.star_mul_eq_coe q

omit [StarRing R] [TrivialStar R] in
private theorem star_mul_self_mul_comm (p q : ℍ[R, a, 0, b]) :
    (star q * q) * p = p * (star q * q) := by
  rw [star_mul_self_eq_coe]; exact QuaternionAlgebra.coe_commutes _ p

omit [StarRing R] [TrivialStar R] in
private theorem mul_star_self_eq_star_mul_self (q : ℍ[R, a, 0, b]) : q * star q = star q * q :=
  (star_comm_self' q).symm

/-! ### Alternativity

The classical fact that makes Cayley-Dickson doubling of an *associative* algebra (here `ℍ`)
produce an *alternative* one: `x * (x * y) = (x * x) * y` and `(y * x) * x = y * (x * x)`. The key
inputs, both about `ℍ` alone, are that the "trace" `p + star p` and "norm" `star q * q = q * star
q` of any quaternion are central scalars (`R`-multiples of `1`, commuting with everything) -- this
is what survives associativity getting lost in the doubling. -/

section Alternative

set_option linter.unusedSectionVars false in
private theorem alternative_left (x y : Octonion R a b c) : x * (x * y) = (x * x) * y := by
  apply Octonion.ext
  · show x.1 * (x * y).1 - c • (star (x * y).2 * x.2) =
      (x * x).1 * y.1 - c • (star y.2 * (x * x).2)
    simp only [mul_fst, mul_snd, star_add, star_mul, star_star, mul_sub,
      sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [← mul_assoc x.1 x.1 y.1]
    have key : x.1 * (star y.2 * x.2) + (star x.1 * star y.2 * x.2 + y.1 * star x.2 * x.2) =
        star x.2 * x.2 * y.1 + (star y.2 * (x.2 * x.1) + star y.2 * (x.2 * star x.1)) := by
      have h1 : (x.1 + star x.1) * (star y.2 * x.2) = (star y.2 * x.2) * (x.1 + star x.1) :=
        add_star_mul_comm x.1 (star y.2 * x.2)
      have h2 : y.1 * (star x.2 * x.2) = (star x.2 * x.2) * y.1 :=
        (star_mul_self_mul_comm y.1 x.2).symm
      calc x.1 * (star y.2 * x.2) + (star x.1 * star y.2 * x.2 + y.1 * star x.2 * x.2)
          = (x.1 + star x.1) * (star y.2 * x.2) + y.1 * (star x.2 * x.2) := by noncomm_ring
        _ = (star y.2 * x.2) * (x.1 + star x.1) + (star x.2 * x.2) * y.1 := by rw [h1, h2]
        _ = star x.2 * x.2 * y.1 + (star y.2 * (x.2 * x.1) + star y.2 * (x.2 * star x.1)) := by
              noncomm_ring
    simp only [sub_sub, ← smul_add]
    rw [key]
  · show (x * y).2 * x.1 + x.2 * star (x * y).1 = y.2 * (x * x).1 + (x * x).2 * star y.1
    simp only [mul_fst, mul_snd, star_sub, star_mul, star_star, QuaternionAlgebra.star_smul',
      mul_sub, add_mul, mul_smul_comm]
    rw [mul_assoc y.2 x.1 x.1]
    have key : x.2 * star y.1 * x.1 + x.2 * (star y.1 * star x.1) - c • (x.2 * (star x.2 * y.2)) =
        x.2 * x.1 * star y.1 + x.2 * star x.1 * star y.1 - c • (y.2 * (star x.2 * x.2)) := by
      have h1 : star y.1 * (x.1 + star x.1) = (x.1 + star x.1) * star y.1 :=
        (add_star_mul_comm x.1 (star y.1)).symm
      have h2 : x.2 * star x.2 * y.2 = y.2 * (star x.2 * x.2) := by
        rw [mul_star_self_eq_star_mul_self, star_mul_self_mul_comm]
      calc x.2 * star y.1 * x.1 + x.2 * (star y.1 * star x.1) - c • (x.2 * (star x.2 * y.2))
          = x.2 * (star y.1 * (x.1 + star x.1)) - c • (x.2 * star x.2 * y.2) := by noncomm_ring
        _ = x.2 * ((x.1 + star x.1) * star y.1) - c • (y.2 * (star x.2 * x.2)) := by
              rw [h1, h2]
        _ = x.2 * x.1 * star y.1 + x.2 * star x.1 * star y.1 - c • (y.2 * (star x.2 * x.2)) := by
              noncomm_ring
    linear_combination (norm := noncomm_ring) key

/-- The right alternative law follows from the left one purely formally, using that `star` is an
involutive anti-automorphism: applying `star` to `alternative_left (star x) (star y) :
star x * (star x * star y) = star x * star x * star y` and simplifying both sides via
`star (a * b) = star b * star a` and `star (star a) = a` turns it exactly into
`(y * x) * x = y * (x * x)`. -/
private theorem alternative_right (x y : Octonion R a b c) : (y * x) * x = y * (x * x) := by
  have h := congrArg star (alternative_left (star x) (star y))
  simpa [star_mul, star_star] using h

instance : IsAlternative (Octonion R a b c) where
  mul_alternative_left := alternative_left
  mul_alternative_right := alternative_right

end Alternative

end StarAspects

/-! ### The `1 x 1` self-adjoint case

The self-adjoint ("Hermitian") elements of `Octonion R a b c` are exactly the scalars: with `2`
invertible, `star x = x` forces every octonion-imaginary coordinate of `x` to vanish, i.e. `x.2 =
0` and `x.1` itself has no quaternion-imaginary part either. This is the degenerate `n = 1` case
of the (here unbuilt, since octonions are non-associative beyond `n = 3`) Hermitian-octonionic-
matrix construction, and it agrees with the `n = 1` case of `RealQM`. -/

section ScalarEmbeddings

variable [Invertible (2 : R)] [StarRing R] [TrivialStar R]

omit [StarRing R] [TrivialStar R] in
private theorem eq_zero_of_neg_eq_self {N : Type*} [AddCommGroup N] [Module R N] {z : N} (hz : -z = z) :
    z = 0 := by
  have h2 : (2 : R) • z = 0 := by
    rw [two_smul, add_eq_zero_iff_eq_neg]; exact hz.symm
  simpa [smul_smul] using congrArg (⅟(2 : R) • ·) h2

/-- The scalar embedding `R → Octonion R a b c`-/
def scalarEmbed : R →+* Octonion R a b c where
  toFun r := mk (algebraMap R ℍ[R, a, 0, b] r) 0
  map_one' := by apply Octonion.ext <;> simp
  map_mul' _ _ := by apply Octonion.ext <;> simp
  map_zero' := by apply Octonion.ext <;> simp
  map_add' _ _ := by apply Octonion.ext <;> simp

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
@[simp] theorem scalarEmbed_fst (r : R) :
    (scalarEmbed r : Octonion R a b c).1 = algebraMap R ℍ[R, a, 0, b] r := rfl

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
@[simp] theorem scalarEmbed_snd (r : R) : (scalarEmbed r : Octonion R a b c).2 = 0 := rfl

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
theorem scalarEmbed_injective :
    Function.Injective (scalarEmbed (R := R) (a := a) (b := b) (c := c)) := by
  intro r s h
  exact QuaternionAlgebra.algebraMap_injective (congrArg Prod.fst h)

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
@[simp] theorem star_scalarEmbed (r : R) :
    star (scalarEmbed r : Octonion R a b c) = scalarEmbed r := by
  apply Octonion.ext <;> simp

/-- The self-adjoint octonions are exactly the scalars: "all imaginary parts are zero", made
precise. -/
theorem isSelfAdjoint_iff (x : Octonion R a b c) : star x = x ↔ ∃ r : R, x = scalarEmbed r := by
  constructor
  · intro hx
    have h2 : x.2 = 0 :=
      eq_zero_of_neg_eq_self (R := R) (N := ℍ[R, a, 0, b]) (congrArg Prod.snd hx)
    have h1 : star x.1 = x.1 := congrArg Prod.fst hx
    have hI : x.1.imI = 0 := eq_zero_of_neg_eq_self (R := R) (z := x.1.imI) (by
      have := congrArg QuaternionAlgebra.imI h1; rwa [QuaternionAlgebra.imI_star] at this)
    have hJ : x.1.imJ = 0 := eq_zero_of_neg_eq_self (R := R) (z := x.1.imJ) (by
      have := congrArg QuaternionAlgebra.imJ h1; rwa [QuaternionAlgebra.imJ_star] at this)
    have hK : x.1.imK = 0 := eq_zero_of_neg_eq_self (R := R) (z := x.1.imK) (by
      have := congrArg QuaternionAlgebra.imK h1; rwa [QuaternionAlgebra.imK_star] at this)
    refine ⟨x.1.re, ?_⟩
    apply Octonion.ext
    · show x.1 = algebraMap R ℍ[R, a, 0, b] x.1.re
      rw [QuaternionAlgebra.algebraMap_eq]
      apply QuaternionAlgebra.ext <;> simp [hI, hJ, hK]
    · exact h2
  · rintro ⟨r, rfl⟩
    exact star_scalarEmbed r

omit [Invertible (2 : R)] in
/-- The octonion norm `x * star x` is a central scalar: the quaternion norm of the first
component, plus `c` times the quaternion norm of the second. This is the composition-algebra fact
that a general octonion doesn't lose in Cayley-Dickson doubling, even though associativity does --
it's the key input still missing for `IsFormallyReal` on the `n x n` Hermitian octonionic matrices
(see the `ThreeByThree` formal-reality remarks). -/
theorem mul_star_self_eq_scalarEmbed (x : Octonion R a b c) :
    x * star x = scalarEmbed ((star x.1 * x.1).re + c * (star x.2 * x.2).re) := by
  apply Octonion.ext
  · show x.1 * (star x).1 - c • (star (star x).2 * x.2) = _
    rw [star_fst, star_snd, star_neg, neg_mul, smul_neg, sub_neg_eq_add,
      mul_star_self_eq_star_mul_self, star_mul_self_eq_coe x.1, star_mul_self_eq_coe x.2,
      scalarEmbed_fst]
    norm_cast
  · show (star x).2 * x.1 + x.2 * star (star x).1 = _
    rw [star_snd, star_fst, star_star, neg_mul, scalarEmbed_snd]
    abel

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
/-- The real part of an octonion product doesn't care about the order of the factors: `Re(xy) =
Re(yx)`, even though `xy` and `yx` themselves genuinely differ. Same brute-force technique as
`re_mul_mul_eq_re_mul_mul` below. -/
theorem re_mul_comm (x y : Octonion R a b c) : (x * y).1.re = (y * x).1.re := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨x1a, x1b, x1c, x1d⟩ := x1
  obtain ⟨x2a, x2b, x2c, x2d⟩ := x2
  obtain ⟨y1a, y1b, y1c, y1d⟩ := y1
  obtain ⟨y2a, y2b, y2c, y2d⟩ := y2
  simp only [mul_fst, QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_sub_mk,
    QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
  ring

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
/-- The real part of a triple product of octonions doesn't depend on how it's associated: `(x*y)*z`
and `x*(y*z)` may genuinely differ (octonions are non-associative), but their real parts agree, so
`Re(x*y*z)` is unambiguous. This is the composition-algebra fact needed to make a
Freudenthal-style cubic form/determinant well-defined for the `n = 3` Hermitian octonionic
matrices -- the next building block after `mul_star_self_eq_scalarEmbed` towards
`ThreeByThree.detTrace`. Proved by brute-force expansion into the `8`-real-coordinate formulas for
Cayley-Dickson multiplication (twice: octonion from quaternion, quaternion from `R`), where the
claim becomes a polynomial identity `ring` can close directly -- no need for the general
alternative-algebra "associator is alternating" theorem. -/
theorem re_mul_mul_eq_re_mul_mul (x y z : Octonion R a b c) :
    ((x * y) * z).1.re = (x * (y * z)).1.re := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  obtain ⟨x1a, x1b, x1c, x1d⟩ := x1
  obtain ⟨x2a, x2b, x2c, x2d⟩ := x2
  obtain ⟨y1a, y1b, y1c, y1d⟩ := y1
  obtain ⟨y2a, y2b, y2c, y2d⟩ := y2
  obtain ⟨z1a, z1b, z1c, z1d⟩ := z1
  obtain ⟨z2a, z2b, z2c, z2d⟩ := z2
  simp only [mul_fst, mul_snd, QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_add_mk,
    QuaternionAlgebra.mk_sub_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.smul_mk,
    smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in
private theorem star_algebraMap (r : R) :
    star (algebraMap R ℍ[R, a, 0, b] r) = algebraMap R ℍ[R, a, 0, b] r := by
  rw [QuaternionAlgebra.algebraMap_eq]
  apply QuaternionAlgebra.ext <;> simp

set_option linter.unusedSectionVars false in
theorem scalarEmbed_mul (r : R) (x : Octonion R a b c) : scalarEmbed r * x = r • x := by
  apply Octonion.ext
  · show algebraMap R ℍ[R, a, 0, b] r * x.1 - c • (star x.2 * (0 : ℍ[R, a, 0, b])) = r • x.1
    rw [mul_zero, smul_zero, sub_zero, Algebra.smul_def]
  · show x.2 * algebraMap R ℍ[R, a, 0, b] r + (0 : ℍ[R, a, 0, b]) * star x.1 = r • x.2
    rw [zero_mul, add_zero, ← Algebra.commutes, Algebra.smul_def]

theorem mul_scalarEmbed (x : Octonion R a b c) (r : R) : x * scalarEmbed r = r • x := by
  apply Octonion.ext
  · show x.1 * algebraMap R ℍ[R, a, 0, b] r - c • (star (0 : ℍ[R, a, 0, b]) * x.2) = r • x.1
    rw [star_zero, zero_mul, smul_zero, sub_zero, ← Algebra.commutes, Algebra.smul_def]
  · show (0 : ℍ[R, a, 0, b]) * x.1 + x.2 * star (algebraMap R ℍ[R, a, 0, b] r) = r • x.2
    rw [zero_mul, zero_add, star_algebraMap, ← Algebra.commutes, Algebra.smul_def]

theorem smul_scalarEmbed (r K : R) :
    r • (scalarEmbed K : Octonion R a b c) = scalarEmbed (r * K) := by
  rw [← scalarEmbed_mul, map_mul]

end ScalarEmbeddings

end Octonion

section OctonionMatrices

variable {R : Type*}
  [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
  {a b c : R}
  {n : Type*} [Fintype n] [DecidableEq n]

abbrev OctonionMatrix : Type _ := Matrix n n (Octonion R a b c)

instance : Star (Octonion R a b c) := inferInstance
instance : Star (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star M := (Matrix.map (f:=star)) M.transpose

instance : StarAddMonoid (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star_involutive M := by
    apply Matrix.ext; intro i j
    simp only [star]
    simp
    rfl
  star_add M N := by
    apply Matrix.ext; intro i j
    show star (M j i + N j i) = star (M j i) + star (N j i)
    exact star_add (M j i) (N j i)

instance : StarMul (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star_mul A B := by
    apply Matrix.ext; intro i j
    simp only [star, Matrix.mul_apply]
    rw [Matrix.conjTranspose_mul]
    rfl

instance : StarModule R (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star_smul := by
    intros r a1
    ext i j <;> simp only [star] <;> simp

instance : IsScalarTower R (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
    (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) := inferInstance

instance : SMulCommClass R (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
    (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) := inferInstance

/-- The Hermitian octonionic `n × n` matrices: those fixed by conjugate-transpose. A `Submodule`
so that `Add`, `Module R`, `Neg`, etc. are inherited for free; `Mul` is defined separately as the
symmetrized product `⅟2 • (AB + BA)`. -/
def HermitianOctonionMatrix : Submodule R (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  carrier := {M | star M = M}
  zero_mem' := star_zero _
  add_mem' {x y} hx hy := by
    have key : (x+y) ∈ {M | star M = M} := by
      simp
      rw [hx.out]
      rw [hy.out]
    exact key
  smul_mem' r x hx := by
    simp
    rw [hx.out]

instance Mul_HermitianOctonionMatrix : Mul (↥(HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))) where
  mul x y := ⟨(⅟2 : R) • (x.1 * y.1 + y.1 * x.1), by
    show star ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1)) = _
    rw [star_smul, star_trivial, star_add]
    rw [add_comm]
    repeat erw [star_mul]
    have hx :
      (x: OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) =
      star (x: OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) := by
      exact x.property.symm
    have hy :
      (y: OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) =
      star (y: OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) := by
      exact y.property.symm
    repeat erw [hx.symm, hy.symm]
  ⟩

omit [Fintype n] [DecidableEq n] in
lemma diag_real
  (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
  (i : n) :
    ∃ r : R, M.val i i = Octonion.scalarEmbed r := by
  have h := congrArg (fun M => M i i) M.property
  exact (Octonion.isSelfAdjoint_iff (M.val i i)).mp h

omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_just_11 (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.re = r := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_1i (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imI = 0 := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_1j (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imJ = 0 := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_1k (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imK = 0 := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_2 (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.2 = 0 := by
  intro h
  simp [h]

omit i2 [StarRing R] [TrivialStar R] in
private lemma transpose_trivial (x: OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1)): x.transpose = x := by
  have subsing : Subsingleton (Fin 1) := by infer_instance
  apply Matrix.ext
  intro i j
  have hi : i.val = 0 := by
    simp
  have hj : j.val = 0 := by
    simp
  have hij : i = j := by
    exact subsing.elim i j
  rw [hij]
  simp

instance CommRing_HermitianOctonionMatrix : NonAssocCommRing (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  __ := (inferInstance : AddCommGroup
    (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)))
  __ := (inferInstance : Mul
    (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)))
  one := ⟨1, by
    change star (1 : OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) = 1
    exact Matrix.conjTranspose_one
  ⟩
  left_distrib x y z := by
    apply Subtype.ext
    change (⅟2 : R) • (x.1 * (y.1 + z.1) + (y.1 + z.1) * x.1) =
      (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) +
        (⅟2 : R) • (x.1 * z.1 + z.1 * x.1)
    rw [mul_add, add_mul, smul_add]
    repeat rw [smul_add]
    abel
  right_distrib x y z := by
    apply Subtype.ext
    change (⅟2 : R) • ((x.1 + y.1) * z.1 + z.1 * (x.1 + y.1)) =
      (⅟2 : R) • (x.1 * z.1 + z.1 * x.1) +
        (⅟2 : R) • (y.1 * z.1 + z.1 * y.1)
    rw [add_mul, mul_add, smul_add]
    repeat rw [smul_add]
    abel
  zero_mul x := by
    apply Subtype.ext
    change (⅟2 : R) • (0 * x.1 + x.1 * 0) = 0
    simp
  mul_zero x := by
    apply Subtype.ext
    change (⅟2 : R) • (x.1 * 0 + 0 * x.1) = 0
    simp
  mul_comm x y := by
    apply Subtype.ext
    change (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) =
      (⅟2 : R) • (y.1 * x.1 + x.1 * y.1)
    rw [add_comm]
  one_mul x := by
    apply Subtype.ext
    change (⅟2 : R) • (1 * x.1 + x.1 * 1) = x.1
    rw [one_mul, mul_one, ← two_smul R x.1, smul_smul, invOf_mul_self, one_smul]
  mul_one x := by
    apply Subtype.ext
    change (⅟2 : R) • (x.1 * 1 + 1 * x.1) = x.1
    rw [mul_one, one_mul, ← two_smul R x.1, smul_smul, invOf_mul_self, one_smul]

/-- `R`-scaling associates with the symmetrized Hermitian product `⅟2 • (AB + BA)`. Not inherited
automatically from `IsScalarTower R (OctonionMatrix ...) (OctonionMatrix ...)`, since `Mul` on
`HermitianOctonionMatrix` is the symmetrized product, not the ambient matrix product. -/
instance IsScalarTower_HermitianOctonionMatrix :
    IsScalarTower R (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
      (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  smul_assoc r x y := by
    apply Subtype.ext
    change (⅟2 : R) • ((r • x.1) * y.1 + y.1 * (r • x.1)) =
      r • ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1))
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_comm (⅟2 : R) r]

/-- `R`-scaling commutes across the symmetrized Hermitian product, for the same reason
`IsScalarTower_HermitianOctonionMatrix` needs its own proof. -/
instance SMulCommClass_HermitianOctonionMatrix :
    SMulCommClass R (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
      (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  smul_comm r x y := by
    apply Subtype.ext
    change r • ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1)) =
      (⅟2 : R) • (x.1 * (r • y.1) + (r • y.1) * x.1)
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_comm r (⅟2 : R)]

instance Star_HermitianOctonionMatrix : Star (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star x := x

instance TrivialStar_HermitianOctonionMatrix : TrivialStar (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star_trivial := by
    intro r
    rfl

end OctonionMatrices

namespace Octonion

section InnerProduct

variable {R : Type*}
variable [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

/-- The underlying function of `innerProduct`: the polarization `⅟2 * (x * star y + y * star x)`
of the octonion norm form, which is self-adjoint for any `x y` (hence a scalar, read off via
`.1.re`). Kept separate from the bundled `innerProduct` so the bilinearity proofs below can be
named lemmas about it rather than inlined terms in a `LinearMap.mk₂` call. -/
private def innerProductFun (x y : Octonion R a b c) : R :=
  ⅟(2 : R) * (x * star y + y * star x).1.re

omit [StarRing R] [TrivialStar R] in
private theorem innerProductFun_add_left (x₁ x₂ y : Octonion R a b c) :
    innerProductFun (x₁ + x₂) y = innerProductFun x₁ y + innerProductFun x₂ y := by
  unfold innerProductFun
  have h : (x₁ + x₂) * star y + y * star (x₁ + x₂) =
      (x₁ * star y + y * star x₁) + (x₂ * star y + y * star x₂) := by
    rw [add_mul, star_add, mul_add]; abel
  rw [h]
  -- `.1` (Prod.fst) and `.re` (`QuaternionAlgebra.reₗ`) are each additive by `rfl` (see
  -- `Octonion.add_fst` and `QuaternionAlgebra.reₗ.map_add'`), so this `show` just forces that
  -- reduction before finishing with `mul_add`.
  show ⅟(2 : R) * ((x₁ * star y + y * star x₁).1.re + (x₂ * star y + y * star x₂).1.re) = _
  rw [mul_add]

private theorem innerProductFun_smul_left (r : R) (x y : Octonion R a b c) :
    innerProductFun (r • x) y = r * innerProductFun x y := by
  unfold innerProductFun
  have h : r • x * star y + y * star (r • x) = r • (x * star y + y * star x) := by
    rw [smul_add]
    rw [smul_mul_assoc]
    rw [star_smul]
    rw [star_trivial (R:=R)]
    rw [mul_smul_comm]
  rw [h]
  show ⅟(2 : R) * (r • (x * star y + y * star x)).1.re = _
  show ⅟(2 : R) * (r * (x * star y + y * star x).1.re) = _
  rw [mul_left_comm]

omit [StarRing R] [TrivialStar R] in
private theorem innerProductFun_add_right (x y₁ y₂ : Octonion R a b c) :
    innerProductFun x (y₁ + y₂) = innerProductFun x y₁ + innerProductFun x y₂ := by
  unfold innerProductFun
  have h : x * star (y₁ + y₂) + (y₁ + y₂) * star x =
      (x * star y₁ + y₁ * star x) + (x * star y₂ + y₂ * star x) := by
    rw [star_add, mul_add, add_mul]; abel
  rw [h]
  show ⅟(2 : R) * ((x * star y₁ + y₁ * star x).1.re + (x * star y₂ + y₂ * star x).1.re) = _
  rw [mul_add]

private theorem innerProductFun_smul_right (r : R) (x y : Octonion R a b c) :
    innerProductFun x (r • y) = r * innerProductFun x y := by
  unfold innerProductFun
  have h : x * star (r • y) + r • y * star x = r • (x * star y + y * star x) := by
    rw [smul_add]
    rw [smul_mul_assoc]
    rw [star_smul]
    rw [star_trivial (R:=R)]
    rw [mul_smul_comm]
  rw [h]
  show ⅟(2 : R) * (r • (x * star y + y * star x)).1.re = _
  show ⅟(2 : R) * (r * (x * star y + y * star x).1.re) = _
  rw [mul_left_comm]

/-- The octonion "inner product", bundled as a bilinear form: the polarization
`⅟2 * (x * star y + y * star x)` of the octonion norm form, which is self-adjoint for any `x y`
(hence a scalar, read off via `.1.re`). This is a fact about pairs of octonions on their own,
independent of any matrix construction -- it feeds the octonion part of the `2 x 2` Hermitian
identification's bilinear form. -/
noncomputable def innerProduct : LinearMap.BilinForm R (Octonion R a b c) :=
  LinearMap.mk₂ R innerProductFun
    innerProductFun_add_left innerProductFun_smul_left
    innerProductFun_add_right innerProductFun_smul_right

set_option linter.unusedSectionVars false in
@[simp] theorem innerProduct_apply (x y : Octonion R a b c) :
    innerProduct (R := R) (a := a) (b := b) (c := c) x y =
      ⅟(2 : R) * (x * star y + y * star x).1.re :=
  rfl

/-- The polarization of `mul_star_self_eq_scalarEmbed`: `x * star y + y * star x` is a central
scalar too, namely `2 * innerProduct x y`. Proved directly from `star_mul`/`star_star` (showing
`x * star y + y * star x` is self-adjoint) rather than by re-deriving `mul_star_self_eq_scalarEmbed`
at `x + y`, since `isSelfAdjoint_iff` already hands us the scalar and `innerProduct_apply` then
pins down its value. -/
theorem mul_star_add_star_mul_eq_scalarEmbed (x y : Octonion R a b c) :
    x * star y + y * star x = scalarEmbed (2 * innerProduct x y) := by
  have hself : star (x * star y + y * star x) = x * star y + y * star x := by
    rw [star_add, star_mul, star_mul, star_star, star_star]
    abel
  obtain ⟨r, hr⟩ := (isSelfAdjoint_iff _).mp hself
  have hre : innerProduct x y = ⅟(2 : R) * r := by
    rw [innerProduct_apply, hr, scalarEmbed_fst]
    rfl
  rw [hr]
  congr 1
  rw [hre, ← mul_assoc, mul_invOf_self, one_mul]

/-- `innerProduct` doesn't see simultaneous conjugation of both arguments: `⟨star x, star y⟩ =
⟨x, y⟩`. Follows from `re_mul_comm` (`Re(xy) = Re(yx)`) applied to the two cross terms. -/
theorem innerProduct_star_star (x y : Octonion R a b c) :
    innerProduct (star x) (star y) = innerProduct x y := by
  simp only [innerProduct_apply, star_star]
  have h1 : (star x * y).1.re = (y * star x).1.re := re_mul_comm _ _
  have h2 : (star y * x).1.re = (x * star y).1.re := re_mul_comm _ _
  have hsum : (star x * y + star y * x).1.re = (x * star y + y * star x).1.re := by
    show (star x * y).1.re + (star y * x).1.re = (x * star y).1.re + (y * star x).1.re
    rw [h1, h2]
    ring
  rw [hsum]

end InnerProduct

/-! ### Comparison with `RealQM`'s `1 x 1` case

`RealQM.symmetricMatrices R (Fin 1)` collapses to plain `R` too (`RealQM.oneRingEquiv`), since a
`1 x 1` matrix is trivially symmetric and the symmetrized product agrees with ordinary
multiplication once there's only one entry. Composing that with `Octonion.scalarEmbed` gives an
explicit embedding of `RealQM`'s `1 x 1` Jordan algebra into the octonions, landing exactly on the
self-adjoint elements: both constructions are literally the same copy of `R`. -/
section OneByOne

variable {R : Type*}
variable [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

private lemma HermitianOctonionMatrixOne.ext_re
    {M N : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1)}
    (h : (M.val 0 0).1.re = (N.val 0 0).1.re) : M = N := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi, hj]
  obtain ⟨rM, hM⟩ := diag_real (R:=R) (a:=a) (b:=b) (c:=c) M 0
  obtain ⟨rN, hN⟩ := diag_real (R:=R) (a:=a) (b:=b) (c:=c) N 0
  have hrM : rM = (M.val 0 0).1.re := by
    rw [hM]
    simp
  have hrN : rN = (N.val 0 0).1.re := by
    rw [hN]
    simp
  rw [hM, hN, hrM, hrN, h]

omit i2 in
private lemma HermitianOctonionMatrixOne.add_re
    (M N : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1)) :
    (((M + N).val 0 0).1.re : R) = (M.val 0 0).1.re + (N.val 0 0).1.re := by
  rfl

private lemma HermitianOctonionMatrixOne.mul_re
    (M N : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1)) :
    ⅟(2 : R) * (((M.val * N.val) 0 0).1.re) +
        ⅟(2 : R) * (((N.val * M.val) 0 0).1.re) =
      (M.val 0 0).1.re * (N.val 0 0).1.re := by
  obtain ⟨rM, hM⟩ := diag_real (R:=R) (a:=a) (b:=b) (c:=c) M 0
  obtain ⟨rN, hN⟩ := diag_real (R:=R) (a:=a) (b:=b) (c:=c) N 0
  have hrM : rM = (M.val 0 0).1.re := by
    rw [hM]
    simp
  have hrN : rN = (N.val 0 0).1.re := by
    rw [hN]
    simp
  have hMN : (((M.val * N.val) 0 0).1.re : R) = rM * rN := by
    simp [Matrix.mul_apply, hM, hN]
  have hNM : (((N.val * M.val) 0 0).1.re : R) = rN * rM := by
    simp [Matrix.mul_apply, hM, hN]
  rw [hMN, hNM]
  rw [mul_comm rN rM]
  rw [hrM, hrN]
  rw [← add_mul]
  rw [← two_mul]
  rw [mul_comm (2 : R) (⅟(2 : R)), ← mul_assoc, invOf_mul_self, one_mul]

/-- The explicit identification of `RealQM`'s `1 x 1` Jordan algebra with the self-adjoint
octonions, both being copies of plain `R`. -/
def ofSymmetricMatricesOne :
  HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1) ≃+* R :=
  { toFun := fun ⟨x,hx⟩ => (x 0 0).1.re
    invFun := fun r => by
      set x : Octonion R a b c := scalarEmbed r
      have hx : x = star x := by
        rw [star_scalarEmbed]
      let xmat : OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) := ![![x]]
      have hxmat : xmat = star xmat := by
        simp only [star]
        apply Matrix.ext
        intro i j
        have hi : i = (0 : Fin 1) := by
          exact Subsingleton.elim _ _
        have hj : j = 0 := by
          exact Subsingleton.elim _ _
        rw [hi,hj]
        unfold xmat
        simp
        have hx2 : x.2 = 0 := by
          exact diag_no_2 x r (rfl)
        have hx1I : x.1.imI = 0 := by
          exact diag_no_1i x r (rfl)
        have hx1J : x.1.imJ = 0 := by
          exact diag_no_1j x r (rfl)
        have hx1K : x.1.imK = 0 := by
          exact diag_no_1k x r (rfl)
        rw [hx2, hx1I, hx1J, hx1K]
        simp
        change x = scalarEmbed x.1.re
        have hx11 : x.1.re = r := by
          exact diag_just_11 x r (rfl)
        rw [hx11]
      have key : xmat ∈ {M | star M = M} := by
        simp
        exact hxmat.symm
      have key2 : xmat ∈ HermitianOctonionMatrix := by
        exact key
      exact ⟨xmat, key2⟩
    left_inv := fun x => by
      apply HermitianOctonionMatrixOne.ext_re
      simp
    right_inv := fun r => by
      simp
    map_mul' := fun x y => by
      simp
      exact HermitianOctonionMatrixOne.mul_re x y
    map_add' := fun x y => by
      exact HermitianOctonionMatrixOne.add_re x y
  }

end OneByOne

/-! ### The `2 x 2` Hermitian octonionic case

The `2 x 2` construction is the spin-factor case, via the usual trace/trace-free split: writing a
Hermitian matrix as `![![r, x], [star x, s]]` with `r s : R` and `x : Octonion R a b c`, the
*scalar* coordinate is the half-trace `t = (r + s) / 2`, and the *vector* coordinate is the
trace-free part `(x, (r - s) / 2) : Octonion R a b c × R` -- **not** simply the two diagonal
entries directly, since only their half-sum survives as the scalar while their half-difference
joins `x` in the vector part. The intended comparison theorem here is an explicit `≃+*`, parallel
to `ofSymmetricMatricesOne`, but landing on `SpinFactor R (Octonion R a b c × R) B` for the
appropriate bilinear form `B`, instead of the `1 x 1` scalar algebra. -/
section TwoByTwo

variable {R : Type*}
variable [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

omit i2 in
/-- The off-diagonal Hermitian-symmetry condition, the `2 x 2` analogue of `diag_real` for the
diagonal: in a Hermitian `2 x 2` octonionic matrix, the `(1,0)` entry is forced to be the
conjugate of the `(0,1)` entry. -/
private lemma HermitianOctonionMatrixTwo.off_diag
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) :
    M.val 1 0 = star (M.val 0 1) := by
  have h : star (M.val 1 0) = M.val 0 1 := congrFun (congrFun M.property 0) 1
  rw [← h, star_star]

/-- The half-trace of a Hermitian `2 x 2` octonionic matrix, `t = (r + s) / 2` where `r, s` are the
(real) diagonal entries -- read off directly via the quaternion real-part coordinate `.1.re`
(matching `diag_just_11`), so this needs no case split on `diag_real`. This is the scalar
coordinate of the intended `SpinFactor` identification; the division by `2` is genuinely needed
here (unlike `off_diag` above), since it must match `SpinFactor`'s fixed `a • y + b • x`
multiplication -- see the discussion above `TwoByTwo`. -/
private def HermitianOctonionMatrixTwo.traceHalf
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) : R :=
  ⅟(2 : R) * ((M.val 0 0).1.re + (M.val 1 1).1.re)

/-- The half-difference of the diagonal entries of a Hermitian `2 x 2` octonionic matrix,
`p = (r - s) / 2`. Together with the off-diagonal octonion `M.val 0 1`, this is the trace-free
"vector" coordinate of the intended `SpinFactor` identification. -/
private def HermitianOctonionMatrixTwo.diffHalf
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) : R :=
  ⅟(2 : R) * ((M.val 0 0).1.re - (M.val 1 1).1.re)

/-- The `(r, s) ↔ (t, p)` change of basis is invertible: given the two (real) diagonal entries
`r, s` produced by `diag_real`, the half-sum/half-difference `traceHalf`/`diffHalf` recover them
back via `r = t + p`, `s = t - p`. This is what makes the trace/trace-free decomposition a genuine
reparametrization of the diagonal data, not merely a one-way projection. -/
private lemma HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) :
    ∃ r s : R, M.val 0 0 = Octonion.scalarEmbed r ∧ M.val 1 1 = Octonion.scalarEmbed s ∧
      r = traceHalf M + diffHalf M ∧ s = traceHalf M - diffHalf M := by
  obtain ⟨r, hr⟩ := diag_real M 0
  obtain ⟨s, hs⟩ := diag_real M 1
  have hr' : (M.val 0 0).1.re = r := diag_just_11 (M.val 0 0) r hr
  have hs' : (M.val 1 1).1.re = s := diag_just_11 (M.val 1 1) s hs
  refine ⟨r, s, hr, hs, ?_, ?_⟩
  · unfold HermitianOctonionMatrixTwo.traceHalf HermitianOctonionMatrixTwo.diffHalf
    rw [hr', hs', ← mul_add]
    have : r + s + (r - s) = 2 * r := by ring
    rw [this, ← mul_assoc, invOf_mul_self, one_mul]
  · unfold HermitianOctonionMatrixTwo.traceHalf HermitianOctonionMatrixTwo.diffHalf
    rw [hr', hs', ← mul_sub]
    have : r + s - (r - s) = 2 * s := by ring
    rw [this, ← mul_assoc, invOf_mul_self, one_mul]

/-- The underlying function of `hermitianTwoBilin`: the octonion polarization form
`Octonion.innerProduct` on the octonion part, plus plain multiplication on the `R` part. Kept
separate so the bilinearity proofs below can be named lemmas, as with `innerProductFun` above. -/
private noncomputable def hermitianTwoBilinFun (z w : Octonion R a b c × R) : R :=
  Octonion.innerProduct z.1 w.1 + z.2 * w.2

private theorem hermitianTwoBilinFun_add_left (z₁ z₂ w : Octonion R a b c × R) :
    hermitianTwoBilinFun (z₁ + z₂) w = hermitianTwoBilinFun z₁ w + hermitianTwoBilinFun z₂ w := by
  unfold hermitianTwoBilinFun
  simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, add_mul]
  abel

private theorem hermitianTwoBilinFun_smul_left (r : R) (z w : Octonion R a b c × R) :
    hermitianTwoBilinFun (r • z) w = r * hermitianTwoBilinFun z w := by
  unfold hermitianTwoBilinFun
  simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_add,
    mul_assoc]

private theorem hermitianTwoBilinFun_add_right (z w₁ w₂ : Octonion R a b c × R) :
    hermitianTwoBilinFun z (w₁ + w₂) = hermitianTwoBilinFun z w₁ + hermitianTwoBilinFun z w₂ := by
  unfold hermitianTwoBilinFun
  simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]
  abel

private theorem hermitianTwoBilinFun_smul_right (r : R) (z w : Octonion R a b c × R) :
    hermitianTwoBilinFun z (r • w) = r * hermitianTwoBilinFun z w := by
  unfold hermitianTwoBilinFun
  simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, mul_add, mul_left_comm]

/-- The bilinear form on the trace-free vector space `Octonion R a b c × R`, making the `2 x 2`
Hermitian identification work. -/
private noncomputable def hermitianTwoBilin :
    LinearMap.BilinForm R (Octonion R a b c × R) :=
  LinearMap.mk₂ R hermitianTwoBilinFun
    hermitianTwoBilinFun_add_left hermitianTwoBilinFun_smul_left
    hermitianTwoBilinFun_add_right hermitianTwoBilinFun_smul_right

private def buildTwo (x : Octonion R a b c) (t p : R) :
    OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2) :=
  !![Octonion.scalarEmbed (t + p), x; star x, Octonion.scalarEmbed (t - p)]

set_option linter.unusedSectionVars false in
private lemma buildTwo_isHermitian (x : Octonion R a b c) (t p : R) :
    star (buildTwo (R:=R) (a:=a) (b:=b) (c:=c) x t p) = buildTwo x t p := by
  apply Matrix.ext
  intro i j
  show star (buildTwo x t p j i) = buildTwo x t p i j
  fin_cases i <;> fin_cases j <;> simp [buildTwo, star_scalarEmbed, star_star]

private lemma traceHalf_buildTwo (x : Octonion R a b c) (t p : R) :
    HermitianOctonionMatrixTwo.traceHalf ⟨buildTwo x t p, buildTwo_isHermitian x t p⟩ = t := by
  show ⅟(2 : R) * ((buildTwo x t p 0 0).1.re + (buildTwo x t p 1 1).1.re) = t
  show ⅟(2 : R) * ((scalarEmbed (t + p) : Octonion R a b c).1.re +
    (scalarEmbed (t - p) : Octonion R a b c).1.re) = t
  rw [scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.algebraMap_eq]
  show ⅟(2 : R) * ((t + p) + (t - p)) = t
  rw [show (t + p) + (t - p) = 2 * t from by ring, ← mul_assoc, invOf_mul_self, one_mul]

private lemma diffHalf_buildTwo (x : Octonion R a b c) (t p : R) :
    HermitianOctonionMatrixTwo.diffHalf ⟨buildTwo x t p, buildTwo_isHermitian x t p⟩ = p := by
  show ⅟(2 : R) * ((buildTwo x t p 0 0).1.re - (buildTwo x t p 1 1).1.re) = p
  show ⅟(2 : R) * ((scalarEmbed (t + p) : Octonion R a b c).1.re -
    (scalarEmbed (t - p) : Octonion R a b c).1.re) = p
  rw [scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.algebraMap_eq]
  show ⅟(2 : R) * ((t + p) - (t - p)) = p
  rw [show (t + p) - (t - p) = 2 * p from by ring, ← mul_assoc, invOf_mul_self, one_mul]

/-- The intended explicit identification of `2 x 2` Hermitian octonionic matrices with the
appropriate `SpinFactor`, parallel to `ofSymmetricMatricesOne`: the scalar coordinate is
`traceHalf`, the vector coordinate is `(M.val 0 1, diffHalf M)`. -/
noncomputable def ofSymmetricMatricesTwo :
    HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2) ≃+*
      SpinFactor R (Octonion R a b c × R)
        (hermitianTwoBilin (R:=R) (a:=a) (b:=b) (c:=c)) where
  toFun M := SpinFactor.mk _ (M.val 0 1, HermitianOctonionMatrixTwo.diffHalf M)
    (HermitianOctonionMatrixTwo.traceHalf M)
  invFun z := ⟨buildTwo z.1.1 z.2 z.1.2, buildTwo_isHermitian z.1.1 z.2 z.1.2⟩
  left_inv M := by
    obtain ⟨r, s, hr, hs, hr', hs'⟩ := HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf M
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    show buildTwo (M.val 0 1) (HermitianOctonionMatrixTwo.traceHalf M)
        (HermitianOctonionMatrixTwo.diffHalf M) i j = M.val i j
    fin_cases i <;> fin_cases j
    · show scalarEmbed (HermitianOctonionMatrixTwo.traceHalf M + HermitianOctonionMatrixTwo.diffHalf M) =
        M.val 0 0
      rw [← hr', hr]
    · rfl
    · show star (M.val 0 1) = M.val 1 0
      exact (HermitianOctonionMatrixTwo.off_diag M).symm
    · show scalarEmbed (HermitianOctonionMatrixTwo.traceHalf M - HermitianOctonionMatrixTwo.diffHalf M) =
        M.val 1 1
      rw [← hs', hs]
  right_inv z := by
    apply SpinFactor.ext
    · show (buildTwo z.1.1 z.2 z.1.2 0 1, HermitianOctonionMatrixTwo.diffHalf
        ⟨buildTwo z.1.1 z.2 z.1.2, buildTwo_isHermitian z.1.1 z.2 z.1.2⟩) = z.1
      rw [diffHalf_buildTwo]
      show (z.1.1, z.1.2) = z.1
      rfl
    · show HermitianOctonionMatrixTwo.traceHalf
        ⟨buildTwo z.1.1 z.2 z.1.2, buildTwo_isHermitian z.1.1 z.2 z.1.2⟩ = z.2
      rw [traceHalf_buildTwo]
  map_mul' M N := by
    obtain ⟨r1, s1, hr1, hs1, hr1', hs1'⟩ :=
      HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf M
    obtain ⟨r2, s2, hr2, hs2, hr2', hs2'⟩ :=
      HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf N
    set t1 := HermitianOctonionMatrixTwo.traceHalf M
    set p1 := HermitianOctonionMatrixTwo.diffHalf M
    set t2 := HermitianOctonionMatrixTwo.traceHalf N
    set p2 := HermitianOctonionMatrixTwo.diffHalf N
    set x1 := M.val 0 1 with hx1
    set x2 := N.val 0 1 with hx2
    have h10 : M.val 1 0 = star x1 := HermitianOctonionMatrixTwo.off_diag M
    have h20 : N.val 1 0 = star x2 := HermitianOctonionMatrixTwo.off_diag N
    have hmul : (M * N).val = (⅟2 : R) • (M.val * N.val + N.val * M.val) := rfl
    have hP01 : (M * N).val 0 1 = t1 • x2 + t2 • x1 := by
      show ((⅟2 : R) • (M.val * N.val + N.val * M.val)) 0 1 = t1 • x2 + t2 • x1
      show (⅟2 : R) • ((M.val * N.val) 0 1 + (N.val * M.val) 0 1) = t1 • x2 + t2 • x1
      have e1 : ⅟(2 : R) * (2 * t1) = t1 := by rw [← mul_assoc, invOf_mul_self, one_mul]
      have e2 : ⅟(2 : R) * (2 * t2) = t2 := by rw [← mul_assoc, invOf_mul_self, one_mul]
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [hr1, hs1, hr2, hs2]
      rw [scalarEmbed_mul, mul_scalarEmbed, scalarEmbed_mul, mul_scalarEmbed]
      rw [hr1', hs1', hr2', hs2']
      rw [show (t1 + p1) • x2 + (t2 - p2) • x1 + ((t2 + p2) • x1 + (t1 - p1) • x2) =
          (2 * t1) • x2 + (2 * t2) • x1 from by module]
      rw [smul_add, smul_smul, smul_smul, e1, e2]
    have hP00 : (M * N).val 0 0 = scalarEmbed (r1 * r2 + innerProduct x1 x2) := by
      show (⅟2 : R) • ((M.val * N.val) 0 0 + (N.val * M.val) 0 0) = _
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [hr1, hr2, h10, h20]
      have hkey : x1 * star x2 + x2 * star x1 = scalarEmbed (2 * innerProduct x1 x2) :=
        mul_star_add_star_mul_eq_scalarEmbed x1 x2
      have hsum : scalarEmbed r1 * scalarEmbed r2 + x1 * star x2 +
          (scalarEmbed r2 * scalarEmbed r1 + x2 * star x1) =
          scalarEmbed (r1 * r2 + r2 * r1 + 2 * innerProduct x1 x2) := by
        rw [map_add, map_add, map_mul, map_mul, ← hkey]
        abel
      rw [hsum, smul_scalarEmbed]
      congr 1
      have expand : r1 * r2 + r2 * r1 + 2 * innerProduct x1 x2 =
          2 * (r1 * r2 + innerProduct x1 x2) := by ring
      rw [expand, ← mul_assoc, invOf_mul_self, one_mul]
    have hP11 : (M * N).val 1 1 = scalarEmbed (s1 * s2 + innerProduct x1 x2) := by
      show (⅟2 : R) • ((M.val * N.val) 1 1 + (N.val * M.val) 1 1) = _
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [hs1, hs2, h10, h20]
      have hkey : star x1 * x2 + star x2 * x1 = scalarEmbed (2 * innerProduct (star x1) (star x2)) := by
        have := mul_star_add_star_mul_eq_scalarEmbed (star x1) (star x2)
        rwa [star_star, star_star] at this
      rw [innerProduct_star_star] at hkey
      have hsum : star x1 * x2 + scalarEmbed s1 * scalarEmbed s2 +
          (star x2 * x1 + scalarEmbed s2 * scalarEmbed s1) =
          scalarEmbed (s1 * s2 + s2 * s1 + 2 * innerProduct x1 x2) := by
        rw [map_add, map_add, map_mul, map_mul, ← hkey]
        abel
      rw [hsum, smul_scalarEmbed]
      congr 1
      have expand : s1 * s2 + s2 * s1 + 2 * innerProduct x1 x2 =
          2 * (s1 * s2 + innerProduct x1 x2) := by ring
      rw [expand, ← mul_assoc, invOf_mul_self, one_mul]
    apply SpinFactor.ext
    · show ((M * N).val 0 1, HermitianOctonionMatrixTwo.diffHalf (M * N)) = t1 • (x2, p2) + t2 • (x1, p1)
      apply Prod.ext
      · exact hP01
      · show HermitianOctonionMatrixTwo.diffHalf (M * N) = t1 * p2 + t2 * p1
        show ⅟(2 : R) * (((M * N).val 0 0).1.re - ((M * N).val 1 1).1.re) = t1 * p2 + t2 * p1
        rw [hP00, hP11, scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq,
          QuaternionAlgebra.algebraMap_eq]
        show ⅟(2 : R) * ((r1 * r2 + innerProduct x1 x2) - (s1 * s2 + innerProduct x1 x2)) =
          t1 * p2 + t2 * p1
        rw [hr1', hs1', hr2', hs2']
        rw [show ((t1 + p1) * (t2 + p2) + innerProduct x1 x2) -
            ((t1 - p1) * (t2 - p2) + innerProduct x1 x2) = 2 * (t1 * p2 + t2 * p1) from by ring,
          ← mul_assoc, invOf_mul_self, one_mul]
    · show HermitianOctonionMatrixTwo.traceHalf (M * N) =
        hermitianTwoBilin (R:=R) (a:=a) (b:=b) (c:=c) (x1, p1) (x2, p2) + t1 * t2
      show ⅟(2 : R) * (((M * N).val 0 0).1.re + ((M * N).val 1 1).1.re) = _
      rw [hP00, hP11, scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq,
        QuaternionAlgebra.algebraMap_eq]
      show ⅟(2 : R) * ((r1 * r2 + innerProduct x1 x2) + (s1 * s2 + innerProduct x1 x2)) =
        hermitianTwoBilinFun (x1, p1) (x2, p2) + t1 * t2
      show ⅟(2 : R) * ((r1 * r2 + innerProduct x1 x2) + (s1 * s2 + innerProduct x1 x2)) =
        (innerProduct x1 x2 + p1 * p2) + t1 * t2
      rw [hr1', hs1', hr2', hs2']
      rw [show ((t1 + p1) * (t2 + p2) + innerProduct x1 x2) +
          ((t1 - p1) * (t2 - p2) + innerProduct x1 x2) =
          2 * (innerProduct x1 x2 + p1 * p2 + t1 * t2) from by ring,
        ← mul_assoc, invOf_mul_self, one_mul]
  map_add' M N := by
    apply SpinFactor.ext
    · show ((M + N).val 0 1, HermitianOctonionMatrixTwo.diffHalf (M + N)) =
        (M.val 0 1, HermitianOctonionMatrixTwo.diffHalf M) +
          (N.val 0 1, HermitianOctonionMatrixTwo.diffHalf N)
      apply Prod.ext
      · rfl
      · show HermitianOctonionMatrixTwo.diffHalf (M + N) =
          HermitianOctonionMatrixTwo.diffHalf M + HermitianOctonionMatrixTwo.diffHalf N
        show ⅟(2 : R) * (((M + N).val 0 0).1.re - ((M + N).val 1 1).1.re) =
          ⅟(2 : R) * ((M.val 0 0).1.re - (M.val 1 1).1.re) +
            ⅟(2 : R) * ((N.val 0 0).1.re - (N.val 1 1).1.re)
        have h00 : ((M + N).val 0 0).1.re = (M.val 0 0).1.re + (N.val 0 0).1.re := rfl
        have h11 : ((M + N).val 1 1).1.re = (M.val 1 1).1.re + (N.val 1 1).1.re := rfl
        rw [h00, h11]
        ring
    · show HermitianOctonionMatrixTwo.traceHalf (M + N) =
        HermitianOctonionMatrixTwo.traceHalf M + HermitianOctonionMatrixTwo.traceHalf N
      show ⅟(2 : R) * (((M + N).val 0 0).1.re + ((M + N).val 1 1).1.re) =
        ⅟(2 : R) * ((M.val 0 0).1.re + (M.val 1 1).1.re) +
          ⅟(2 : R) * ((N.val 0 0).1.re + (N.val 1 1).1.re)
      have h00 : ((M + N).val 0 0).1.re = (M.val 0 0).1.re + (N.val 0 0).1.re := rfl
      have h11 : ((M + N).val 1 1).1.re = (M.val 1 1).1.re + (N.val 1 1).1.re := rfl
      rw [h00, h11]
      ring

end TwoByTwo

/-! ### The `3 x 3` Hermitian octonionic case

The `3 x 3` construction is the exceptional Hermitian octonionic Jordan algebra.
It uses the same ambient matrix type and symmetrized product
but no associative matrix algebra so `HermitianJordan.ofInvolutiveAlgebra` does not apply. -/
section ThreeByThree

variable {R : Type*}
variable [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

abbrev AlbertAlgebra := HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 3)

instance ofAlbert : JordanAlgebra R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) where
  jordan_mul_comm := by
    intro x y
    apply Subtype.ext
    change (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) =
      (⅟2 : R) • (y.1 * x.1 + x.1 * y.1)
    rw [add_comm]
  jordan_identity x y := sorry

/-! ### Formal reality

Over an ordered `R`, with each Cayley-Dickson step's structure constant negative
(`a < 0`, `b < 0`, generalizing Hamilton's quaternions, and `c < 0` for the final octonion
doubling step, generalizing `a = b = c = -1`), the octonion norm form should be positive-definite,
and `trace(A * A)` for a Hermitian `A` should decompose into a sum of those norms over the
entries -- exactly as in `ComplexQM.isFormallyReal`/`QuaternionicQM.isFormallyReal`.

Unlike those cases, that decomposition isn't yet available here: it needs `x * star x` to be a
genuine central scalar (`= Octonion.scalarEmbed (N x)` for some norm form `N`) for *every*
octonion `x`, not just the polarized/diagonal-entry facts already established (`innerProduct`,
`isSelfAdjoint_iff`). That is a composition-algebra fact in its own right (needs the alternative
laws, `IsAlternative`), not yet proved anywhere in this file. -/

section FormallyReal

variable [LinearOrder R] [IsStrictOrderedRing R]

theorem isFormallyReal (ha : a < 0) (hb : b < 0) (hc : c < 0) :
    IsFormallyReal R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) := by
  sorry

/-- Rank `3`, matching the classical Albert algebra. Stubbed alongside `isFormallyReal` above:
unlike the associative `RealQM`/`ComplexQM`/`QuaternionicQM` cases, octonion non-associativity
means there's no analogue of `MooreDeterminant`'s recursion to fall back on either -- the cyclic
product step in `orbitProd` genuinely uses associativity of the entries, which octonions don't
have. A genuine determinant here needs its own, octonion-specific construction (classically, the
Freudenthal/Jordan cubic form). -/
noncomputable def detTrace (ha : a < 0) (hb : b < 0) (hc : c < 0) :
    @IsFormallyRealDetTrace R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) _ _
      (isFormallyReal ha hb hc) := by
  sorry

end FormallyReal

end ThreeByThree

end Octonion
