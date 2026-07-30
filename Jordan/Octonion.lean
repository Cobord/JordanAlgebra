import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Jordan.Alternative
import Jordan.NuclearInvolution

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

/-- `Octonion R a b c` is a free `R`-module, inherited from `ℍ[R, a, 0, b]`'s own `basisOneIJK`
(via `Module.Free.prod`), the same way `AddCommGroup`/`Module` above are copied across the `def`
barrier from the underlying product type. This is what ultimately lets `AlbertAlgebra` below be
shown free, without needing `R` to be a PID for a submodule-of-free-is-free argument. -/
instance : Module.Free R (Octonion R a b c) :=
  (inferInstance : Module.Free R (ℍ[R, a, 0, b] × ℍ[R, a, 0, b]))

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
/-- The flip of `mul_star_self_eq_scalarEmbed`: `star x * x` is the *same* central scalar as `x *
star x`. Obtained by applying `mul_star_self_eq_scalarEmbed` to `star x` itself and simplifying the
result back down via `star_star`/`mul_star_self_eq_star_mul_self` (at the quaternion level, on
`x.1`) -- not a new composition-algebra input. -/
theorem star_mul_self_eq_scalarEmbed (x : Octonion R a b c) :
    star x * x = scalarEmbed ((star x.1 * x.1).re + c * (star x.2 * x.2).re) := by
  have h := mul_star_self_eq_scalarEmbed (star x)
  rw [star_star] at h
  rw [h]
  congr 2
  · rw [star_fst, star_star, mul_star_self_eq_star_mul_self]
  · rw [star_snd, star_neg, neg_mul]
    rw [mul_neg, neg_neg]

omit [Invertible (2 : R)] in
/-- The octonion trace `x + star x` is a central scalar, exactly `2 * Re(x)` -- the octonion
analogue of `add_star_eq_coe` for quaternions. Combined with `mul_alternative_right`, this is what
lets a `star y` sitting next to a product be traded for a plain (unstarred) `y`, e.g. `(u * y) *
star y = (2 * Re y) • (u * y) - u * (y * y)`: since `star y = scalarEmbed (2 * Re y) - y`, expanding
`(u * y) * star y` this way needs only the right alternative law `(u * y) * y = u * (y * y)`, not
any genuine Moufang identity. -/
theorem add_star_eq_scalarEmbed (x : Octonion R a b c) :
    x + star x = scalarEmbed (2 * x.1.re) := by
  apply Octonion.ext
  · show x.1 + star x.1 = algebraMap R ℍ[R, a, 0, b] (2 * x.1.re)
    rw [add_star_eq_coe, QuaternionAlgebra.algebraMap_eq]
    rfl
  · show x.2 + (star x).2 = (0 : ℍ[R, a, 0, b])
    rw [star_snd]
    abel

omit [Invertible (2 : R)] in
/-- `star x` is an `R`-affine combination of `x` and `1`: the octonion analogue of solving
`add_star_eq_scalarEmbed` for `star x`. -/
theorem star_eq_scalarEmbed_sub (x : Octonion R a b c) :
    star x = scalarEmbed (2 * x.1.re) - x := by
  rw [← add_star_eq_scalarEmbed]
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

section Nuclear

variable (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0)
  (hc : ∀ x : R, c * x = 0 → x = 0)

omit ha hb hc [StarRing R] [TrivialStar R] in
private theorem eq_zero_of_two_mul_eq_zero {v : R} (h : (2 : R) * v = 0) : v = 0 :=
  (isUnit_of_invertible (2 : R)).mul_right_eq_zero.mp h

omit ha hb hc in
set_option linter.unusedSectionVars false in
/-- A quaternion commuting with both `i` and `j` (hence, since `k = i*j`, with everything) is a
plain scalar. The "commutes with `i`" half already pins the `imI`/`imJ` coordinates to `0`
(no regularity needed); the `imK` coordinate needs *either* `a` or `b` regular to cancel. -/
private theorem quaternion_eq_coe_of_comm_i_j
    (hab : (∀ x : R, a * x = 0 → x = 0) ∨ (∀ x : R, b * x = 0 → x = 0)) (p : ℍ[R, a, 0, b])
    (hi : p * (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b]) = (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b]) * p)
    (hj : p * (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b]) = (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b]) * p) :
    p = algebraMap R ℍ[R, a, 0, b] p.re := by
  obtain ⟨w, x, y, z⟩ := p
  simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, zero_mul, mul_one, one_mul, add_zero,
    zero_add, sub_zero, QuaternionAlgebra.ext_iff] at hi hj
  obtain ⟨-, -, hi3, hi4⟩ := hi
  obtain ⟨-, hj2, -, hj4⟩ := hj
  have hy : y = 0 := eq_zero_of_two_mul_eq_zero (v := y) (by linear_combination -hi4)
  have hx : x = 0 := eq_zero_of_two_mul_eq_zero (v := x) (by linear_combination hj4)
  have hz : z = 0 := by
    rcases hab with ha | hb
    · exact ha z (eq_zero_of_two_mul_eq_zero (v := a * z) (by linear_combination -hi3))
    · exact hb z (eq_zero_of_two_mul_eq_zero (v := b * z) (by linear_combination hj2))
  rw [QuaternionAlgebra.algebraMap_eq]
  exact QuaternionAlgebra.ext rfl hx hy hz

include ha hb hc in
set_option linter.unusedSectionVars false in
theorem nuclear_rpart (n : Octonion R a b c) (hn : IsNuclear n) :
    ∃ r : R, n = scalarEmbed r := by
  have step1 : ∀ q : ℍ[R, a, 0, b], n.1 * q = q * n.1 := by
    intro q
    have h := (hn (mk q 0) (mk 0 1)).1
    unfold IsAlternative.associator at h
    have heq := sub_eq_zero.mp h
    have h2 := congrArg (·.2) heq
    simp only [mul_fst, mul_snd, mk_fst, mk_snd, star_zero, smul_zero, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero, one_mul] at h2
    exact h2
  have step2 : ∀ q : ℍ[R, a, 0, b], c • (star q * n.2 - n.2 * star q) = 0 := by
    intro q
    have h := (hn (mk q 0) (mk 0 1)).1
    unfold IsAlternative.associator at h
    have heq := sub_eq_zero.mp h
    have h1 := congrArg (·.1) heq
    simp only [mul_fst, mul_snd, mk_fst, mk_snd, star_zero, star_one, smul_zero, mul_zero,
      zero_mul, add_zero, zero_add, sub_zero, one_mul] at h1
    rw [zero_sub, zero_sub] at h1
    have h1' : c • (n.2 * star q) = c • (star q * n.2) := neg_inj.mp h1
    rw [smul_sub, sub_eq_zero]
    exact h1'.symm
  have hcmod : ∀ v : ℍ[R, a, 0, b], c • v = 0 → v = 0 := by
    intro v hv
    obtain ⟨w, x, y, z⟩ := v
    simp [QuaternionAlgebra.ext_iff] at hv
    obtain ⟨h1, h2, h3, h4⟩ := hv
    exact QuaternionAlgebra.ext (hc w h1) (hc x h2) (hc y h3) (hc z h4)
  have step2' : ∀ q : ℍ[R, a, 0, b], n.2 * q = q * n.2 := by
    intro q
    have h := hcmod _ (step2 (star q))
    rw [star_star] at h
    exact (sub_eq_zero.mp h).symm
  have n1eq : n.1 = algebraMap R ℍ[R, a, 0, b] n.1.re :=
    quaternion_eq_coe_of_comm_i_j (Or.inl ha) n.1 (step1 ⟨0, 1, 0, 0⟩) (step1 ⟨0, 0, 1, 0⟩)
  have n2eq : n.2 = algebraMap R ℍ[R, a, 0, b] n.2.re :=
    quaternion_eq_coe_of_comm_i_j (Or.inl ha) n.2 (step2' ⟨0, 1, 0, 0⟩) (step2' ⟨0, 0, 1, 0⟩)
  have step3raw :
      (n.2 * star (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b])) * star (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b]) =
      (n.2 * star (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b])) * star (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b]) := by
    have h := (hn (mk (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b]) 0) (mk (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b]) 0)).1
    unfold IsAlternative.associator at h
    have heq := sub_eq_zero.mp h
    have h2 := congrArg (·.2) heq
    simp only [mul_fst, mul_snd, mk_fst, mk_snd, star_zero, smul_zero, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero] at h2
    rw [h2, star_mul, mul_assoc]
  have hqiqj : (star (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b])) * star (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b]) =
      (⟨0, 0, 0, 1⟩ : ℍ[R, a, 0, b]) := by
    simp [QuaternionAlgebra.mk_mul_mk]
  have hqjqi : (star (⟨0, 0, 1, 0⟩ : ℍ[R, a, 0, b])) * star (⟨0, 1, 0, 0⟩ : ℍ[R, a, 0, b]) =
      -(⟨0, 0, 0, 1⟩ : ℍ[R, a, 0, b]) := by
    simp [QuaternionAlgebra.mk_mul_mk]
  have step3 : n.2.re • (⟨0, 0, 0, 1⟩ : ℍ[R, a, 0, b]) =
      -(n.2.re • (⟨0, 0, 0, 1⟩ : ℍ[R, a, 0, b])) := by
    have h := step3raw
    rw [n2eq, ← Algebra.smul_def, ← Algebra.smul_def, smul_mul_assoc, smul_mul_assoc, hqiqj,
      hqjqi, smul_neg] at h
    exact h
  have hn2re : n.2.re = 0 := by
    have hk0 : n.2.re • (⟨0, 0, 0, 1⟩ : ℍ[R, a, 0, b]) = 0 :=
      eq_zero_of_neg_eq_self (R := R) step3.symm
    have := congrArg QuaternionAlgebra.imK hk0
    simpa using this
  refine ⟨n.1.re, ?_⟩
  apply Octonion.ext
  · rw [scalarEmbed_fst]; exact n1eq
  · rw [scalarEmbed_snd, n2eq, hn2re, map_zero]

/-- Octonions form a nuclear involution (`Jordan.NuclearInvolution`): every star-fixed (self-
adjoint) octonion is exactly a `scalarEmbed r` (`isSelfAdjoint_iff`), and scalars associate
trivially with everything, in any argument slot, via `scalarEmbed_mul`/`mul_scalarEmbed` plus the
`smul_mul_assoc`/`mul_smul_comm` scalar-tower laws. The `isNuclear_comm` field (the nucleus is
closed under commutators) needs `nuclear_rpart` (Nuc ⊆ Center), which in turn needs `a`, `b`, `c`
to be non-zero-divisors -- see `JORDAN_IDENTITY_PLAN.md`. -/
@[reducible] def nuclearInvolution : IsNuclearInvolution (Octonion R a b c) where
  isNuclear_of_star_eq x hx := by
    obtain ⟨r, rfl⟩ := (isSelfAdjoint_iff x).mp hx
    exact fun y z =>
      ⟨by unfold IsAlternative.associator
          rw [scalarEmbed_mul, scalarEmbed_mul, smul_mul_assoc]; abel,
       by unfold IsAlternative.associator
          rw [mul_scalarEmbed, scalarEmbed_mul, smul_mul_assoc, mul_smul_comm]; abel,
       by unfold IsAlternative.associator
          rw [mul_scalarEmbed, mul_scalarEmbed, mul_smul_comm]; abel⟩
  isNuclear_comm n x hn := by
    obtain ⟨r, rfl⟩ := nuclear_rpart ha hb hc n hn
    rw [scalarEmbed_mul, mul_scalarEmbed, sub_self]
    exact fun y z =>
      ⟨by unfold IsAlternative.associator; simp,
       by unfold IsAlternative.associator; simp,
       by unfold IsAlternative.associator; simp⟩

end Nuclear

/-- Trading a `star y` sitting to the right of a product for a plain `y`: `(u * y) * star y = (2 *
Re y) • (u * y) - u * (y * y)`. Needs only the right alternative law `(u * y) * y = u * (y * y)`
(`alternative_right`) plus `star_eq_scalarEmbed_sub`, not any genuine Moufang identity -- this is
the key tool for resolving cross terms like `(p * t) * star t` (two independent off-diagonal
octonion matrix entries `p`, `t`) that show up when expanding `jordan_identity` on `AlbertAlgebra`. -/
theorem mul_mul_star_eq (u y : Octonion R a b c) :
    (u * y) * star y = (2 * y.1.re) • (u * y) - u * (y * y) := by
  rw [star_eq_scalarEmbed_sub, mul_sub, mul_scalarEmbed, alternative_right y u]

/-- The mirror-image tool to `mul_mul_star_eq`, trading a `star y` sitting to the left of a product
for a plain `y`: `star y * (y * u) = (2 * Re y) • (y * u) - (y * y) * u`. Needs only the left
alternative law `y * (y * u) = (y * y) * u` (`alternative_left`). -/
theorem star_mul_mul_eq (y u : Octonion R a b c) :
    star y * (y * u) = (2 * y.1.re) • (y * u) - (y * y) * u := by
  rw [star_eq_scalarEmbed_sub, sub_mul, scalarEmbed_mul, alternative_left y u]

/-- The two remaining "sandwich" positions, completing the set alongside `mul_mul_star_eq`/
`star_mul_mul_eq`: here `star y` sits *between* `y` and `u` (rather than on the outside), so this
needs the left alternative law `y * (y * u) = (y * y) * u` (`alternative_left`) instead. -/
theorem mul_star_mul_eq (y u : Octonion R a b c) :
    y * (star y * u) = (2 * y.1.re) • (y * u) - (y * y) * u := by
  rw [star_eq_scalarEmbed_sub, sub_mul, scalarEmbed_mul, mul_sub, mul_smul_comm, alternative_left y u]

/-- The mirror-image tool to `mul_star_mul_eq`, with `star y` again sandwiched between `u` and `y`
but on the other side; needs the right alternative law `(u * y) * y = u * (y * y)`
(`alternative_right`). -/
theorem mul_star_mul_eq' (u y : Octonion R a b c) :
    (u * star y) * y = (2 * y.1.re) • (u * y) - u * (y * y) := by
  rw [star_eq_scalarEmbed_sub, mul_sub, mul_scalarEmbed, sub_mul, smul_mul_assoc,
    alternative_right y u]

/-- `y * y` itself is *not* central in general (unlike `y * star y`), but it decomposes into a
central part plus a multiple of `y`: `y * y = (2 * Re y) • y - y * star y`. Follows from the same
`star y = scalarEmbed (2 * Re y) - y` substitution, this time applied to `y * star y` itself and
solved for `y * y`. This is the missing piece that lets each of the four "sandwich" identities
above collapse all the way down to a genuine central scalar, instead of stopping at the
intermediate `(y * y) * u`/`u * (y * y)` form: see `mul_star_mul_eq_center` etc. below. -/
theorem mul_self_eq (y : Octonion R a b c) :
    y * y = (2 * y.1.re) • y - y * star y := by
  rw [star_eq_scalarEmbed_sub, mul_sub, mul_scalarEmbed]
  abel

/-- The fully-collapsed form of `mul_star_mul_eq`: substituting `mul_self_eq` into
`(y * y) * u` makes the `(2 * Re y) • (y * u)` terms cancel exactly, leaving just the central
scalar `y * star y` acting on `u`. This (and its three mirror-image forms just below) is the
identity actually needed to resolve octonion cross terms in `jordan_identity` -- the
intermediate, uncollapsed `mul_star_mul_eq`/`mul_mul_star_eq`/`star_mul_mul_eq`/`mul_star_mul_eq'`
forms leave genuinely unmatched leftover terms when two *different* off-diagonal entries meet. -/
theorem mul_star_mul_eq_center (y u : Octonion R a b c) :
    y * (star y * u) = ((star y.1 * y.1).re + c * (star y.2 * y.2).re) • u := by
  rw [mul_star_mul_eq, mul_self_eq, sub_mul, smul_mul_assoc, sub_sub_cancel,
    mul_star_self_eq_scalarEmbed, scalarEmbed_mul]

/-- The `(u * y) * star y` mirror of `mul_star_mul_eq_center`. -/
theorem mul_mul_star_eq_center (u y : Octonion R a b c) :
    (u * y) * star y = ((star y.1 * y.1).re + c * (star y.2 * y.2).re) • u := by
  rw [mul_mul_star_eq, mul_self_eq, mul_sub, mul_smul_comm, sub_sub_cancel,
    mul_star_self_eq_scalarEmbed, mul_scalarEmbed]

/-- The `star y * (y * u)` mirror of `mul_star_mul_eq_center`. -/
theorem star_mul_mul_eq_center (y u : Octonion R a b c) :
    star y * (y * u) = ((star y.1 * y.1).re + c * (star y.2 * y.2).re) • u := by
  rw [star_mul_mul_eq, mul_self_eq, sub_mul, smul_mul_assoc, sub_sub_cancel,
    mul_star_self_eq_scalarEmbed, scalarEmbed_mul]

/-- The `(u * star y) * y` mirror of `mul_star_mul_eq_center`. -/
theorem mul_star_mul_eq'_center (u y : Octonion R a b c) :
    (u * star y) * y = ((star y.1 * y.1).re + c * (star y.2 * y.2).re) • u := by
  rw [mul_star_mul_eq', mul_self_eq, mul_sub, mul_smul_comm, sub_sub_cancel,
    mul_star_self_eq_scalarEmbed, mul_scalarEmbed]

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
theorem mul_both_scalarEmbed (r s : R) :
    scalarEmbed r * (scalarEmbed s : Octonion R a b c) = scalarEmbed (r * s) :=
  (map_mul scalarEmbed r s).symm

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
theorem add_both_scalarEmbed (r s : R) :
    scalarEmbed r + (scalarEmbed s : Octonion R a b c) = scalarEmbed (r + s) :=
  (map_add scalarEmbed r s).symm

end ScalarEmbeddings

end Octonion

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

theorem innerProduct_comm (x y : Octonion R a b c) : innerProduct x y = innerProduct y x := by
  simp only [innerProduct_apply, add_comm]

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

/-- `innerProduct` is `R`-homogeneous in its right argument -- immediate from `innerProduct` being
bundled as a `LinearMap.BilinForm`. -/
theorem innerProduct_smul_right (r : R) (x y : Octonion R a b c) :
    innerProduct x (r • y) = r * innerProduct x y := by
  rw [map_smul, smul_eq_mul]

/-- `innerProduct` is "self-adjoint" with respect to left multiplication: `⟨x*y, z⟩ = ⟨x, z*ȳ⟩`.
Purely a consequence of `re_mul_mul_eq_re_mul_mul` (applied to both cross terms of
`innerProduct_apply`'s polarization), no brute-force coordinate expansion needed. -/
theorem innerProduct_mul_right (x y z : Octonion R a b c) :
    innerProduct (x * y) z = innerProduct x (z * star y) := by
  simp only [innerProduct_apply, star_mul, star_star]
  congr 1
  show ((x * y) * star z).1.re + (z * (star y * star x)).1.re =
      (x * (y * star z)).1.re + ((z * star y) * star x).1.re
  rw [re_mul_mul_eq_re_mul_mul x y (star z), re_mul_mul_eq_re_mul_mul z (star y) (star x)]

/-- The mirror of `innerProduct_mul_right`, adjoint with respect to right multiplication instead:
`⟨x*y, z⟩ = ⟨y, x̄*z⟩`. Needs `re_mul_comm` in addition to `re_mul_mul_eq_re_mul_mul`, since the
factor being pulled out is on the *outside* of the product rather than matching
`re_mul_mul_eq_re_mul_mul`'s shape directly. -/
theorem innerProduct_mul_left (x y z : Octonion R a b c) :
    innerProduct (x * y) z = innerProduct y (star x * z) := by
  simp only [innerProduct_apply, star_mul, star_star]
  congr 1
  show ((x * y) * star z).1.re + (z * (star y * star x)).1.re =
      (y * (star z * x)).1.re + ((star x * z) * star y).1.re
  rw [re_mul_comm (x * y) (star z), ← re_mul_mul_eq_re_mul_mul (star z) x y,
    re_mul_comm (star z * x) y, re_mul_comm z (star y * star x),
    re_mul_mul_eq_re_mul_mul (star y) (star x) z, re_mul_comm (star y) (star x * z)]

omit [Invertible (2 : R)] in
/-- `(x * star x).1.re`, unfolded to the same `(star x.1 * x.1).re + c * (star x.2 * x.2).re` form
`mul_mul_star_eq_center`/`mul_star_mul_eq_center` already produce, so those two forms can be
matched up by `rw` without pulling in `OctonionMatrix`'s `diag_just_11`. -/
theorem re_mul_star_self (x : Octonion R a b c) :
    (x * star x).1.re = (star x.1 * x.1).re + c * (star x.2 * x.2).re := by
  rw [mul_star_self_eq_scalarEmbed]
  simp [scalarEmbed_fst]

omit [Invertible (2 : R)] in
/-- The `star`-conjugate mirror of `re_mul_star_self`, for `(star x * x).1.re` instead. -/
theorem re_star_mul_self (x : Octonion R a b c) :
    (star x * x).1.re = (star x.1 * x.1).re + c * (star x.2 * x.2).re := by
  rw [star_mul_self_eq_scalarEmbed]
  simp [scalarEmbed_fst]

/-- `⟨x*y, z*y⟩ = ⟨y*star y⟩ • ⟨x,z⟩` (writing `⟨y*star y⟩` for its real coefficient). Follows from
`innerProduct_mul_right` (peeling the shared `y` off the left) and `mul_mul_star_eq_center`
(collapsing the resulting `(z*y)*star y` sandwich), no brute force. -/
theorem innerProduct_mul_mul_star (x y z : Octonion R a b c) :
    innerProduct (x * y) (z * y) = (y * star y).1.re * innerProduct x z := by
  rw [innerProduct_mul_right x y (z * y), mul_mul_star_eq_center, innerProduct_smul_right,
    re_mul_star_self]

/-- Mirror of `innerProduct_mul_mul_star` for a repeated factor on the *left* instead of the right:
`⟨y*x, y*z⟩ = ⟨star y*y⟩ • ⟨x,z⟩`. -/
theorem innerProduct_mul_mul_star_left (x y z : Octonion R a b c) :
    innerProduct (y * x) (y * z) = (star y * y).1.re * innerProduct x z := by
  rw [innerProduct_mul_left y x (y * z), star_mul_mul_eq_center, innerProduct_smul_right,
    re_star_mul_self]

/-- The mirror cross-term fact to `innerProduct_mul_mul_star`, for the other way a repeated factor
`y` can sandwich a `star x`: `⟨y, z*(star x*y)⟩ = ⟨y*star y⟩ • ⟨x,z⟩`. Follows from
`innerProduct_comm`/`innerProduct_mul_right` (peeling `y` off, via the right this time) and
`mul_star_mul_eq_center`. -/
theorem innerProduct_conj_sandwich (x y z : Octonion R a b c) :
    innerProduct y (z * (star x * y)) = (y * star y).1.re * innerProduct x z := by
  rw [innerProduct_comm y (z * (star x * y)), innerProduct_mul_right z (star x * y) y, star_mul,
    star_star, mul_star_mul_eq_center, innerProduct_smul_right, innerProduct_comm z x,
    re_mul_star_self]

/-- `⟨t, star o * q⟩` and `⟨q, o * t⟩` are the same value, under two layers of
`innerProduct_star_star`. -/
theorem innerProduct_swap_bridge (q t o : Octonion R a b c) :
    innerProduct t (star o * q) = innerProduct q (o * t) := by
  rw [innerProduct_comm t (star o * q), innerProduct_mul_right (star o) q t,
    show t * star q = star (q * star t) from by rw [star_mul, star_star],
    innerProduct_star_star, innerProduct_comm o (q * star t), innerProduct_mul_right q (star t) o,
    star_star]

end InnerProduct

end Octonion
