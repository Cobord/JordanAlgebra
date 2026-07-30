import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Alternative magmas

An *alternative* magma satisfies the two weaker laws that survive Cayley-Dickson doubling of an
associative algebra (e.g. the octonions, doubled from the associative quaternions): `x * (x * y) =
(x * x) * y` and `(y * x) * x = y * (x * x)`. Mathlib has no class for this notion yet.

This file only develops what is generic to *any* `IsAlternative` non-unital non-associative ring,
independent of any particular instance: the associator `(x,y,z) := (x*y)*z - x*(y*z)` is additive
in each argument (free, from distributivity alone), and the two alternative laws say it vanishes
whenever the first two, respectively last two, arguments agree. Linearizing each of those (`x ↦ x +
z` in the repeated slot) shows the associator changes sign under swapping the first two arguments,
and likewise the last two -- and combining those two swaps derives the classical *flexible law*
`x * (y * x) = (x * y) * x`, along with the fact that swapping the outer two arguments also
negates the associator (so the associator is alternating under all of `S₃`, not just the two
adjacent transpositions built in by definition).

Octonion-specific consequences (e.g. anything using `star`) belong in `Jordan.Octonion`, not here.
-/

/-- An *alternative* magma: multiplication need not be associative, but it satisfies the two
weaker laws that survive Cayley-Dickson doubling of an associative algebra (such as the octonions,
doubled from the associative quaternions). Mathlib has no class for this notion yet. -/
class IsAlternative (M : Type*) [Mul M] : Prop where
  /-- The left alternative law: `x * (x * y) = (x * x) * y`. -/
  mul_alternative_left : ∀ x y : M, x * (x * y) = (x * x) * y
  /-- The right alternative law: `(y * x) * x = y * (x * x)`. -/
  mul_alternative_right : ∀ x y : M, (y * x) * x = y * (x * x)

/-- Every associative multiplication is alternative: both alternative laws are then just special
cases of `mul_assoc`. Low priority so it never shadows a bespoke `IsAlternative` instance (e.g.
`Octonion.instIsAlternative`, whose whole point is that `Octonion` is alternative *without* being
associative) when both would otherwise apply. -/
instance (priority := 100) ofSemigroup {M : Type*} [Semigroup M] : IsAlternative M where
  mul_alternative_left x y := (mul_assoc x x y).symm
  mul_alternative_right x y := mul_assoc y x x

namespace IsAlternative

variable {M : Type*} [NonUnitalNonAssocRing M]

/-- The associator `(x*y)*z - x*(y*z)`, vanishing exactly when `x`, `y`, `z` can be multiplied in
either order unambiguously. Defined for any non-unital non-associative ring, with no reference to
`IsAlternative` -- the additivity lemmas just below hold unconditionally; it's only the *vanishing*
facts further down that need `IsAlternative`. -/
def associator (x y z : M) : M := (x * y) * z - x * (y * z)

theorem associator_add_left (x y z w : M) :
    associator (x + y) z w = associator x z w + associator y z w := by
  unfold associator
  simp only [add_mul]
  abel

theorem associator_add_mid (x y z w : M) :
    associator x (y + z) w = associator x y w + associator x z w := by
  unfold associator
  simp only [add_mul, mul_add]
  abel

theorem associator_add_right (x y z w : M) :
    associator x y (z + w) = associator x y z + associator x y w := by
  unfold associator
  simp only [mul_add]
  abel

/-- Teichmüller's identity: holds in *any* non-unital non-associative ring, no alternativity
needed at all -- it's a pure consequence of the associator's definition and distributivity. -/
theorem teichmuller (x y z w : M) :
    associator (x * y) z w - associator x (y * z) w + associator x y (z * w) =
      associator x y z * w + x * associator y z w := by
  unfold associator
  simp only [sub_mul, mul_sub]
  abel

/-- **McCrimmon's (1.1.1)**: the associator of the "plus"-algebra built from *any* non-unital
non-associative ring `M` via the brace product `{x,y} := x*y + y*x` (the doubled Jordan product),
expressed purely in terms of `M`'s own associator and the ordinary commutator. Holds in any linear
algebra, alternative or not -- pure distributivity, no alternative law needed (this is where
`M`'s own Jordan-identity-style computations, e.g. for `AlbertAlgebra`'s symmetrized product,
could in principle reduce to associator identities of the underlying alternative coordinate
algebra uniformly, rather than per-entry matrix bashing -- see `JORDAN_IDENTITY_PLAN.md`). -/
theorem plus_associator_eq (x y z : M) :
    (x * y + y * x) * z + z * (x * y + y * x) - (x * (y * z + z * y) + (y * z + z * y) * x)
      = (associator x y z - associator z y x) + (associator y x z - associator z x y)
        + (associator x z y - associator y z x) + (y * (x * z - z * x) - (x * z - z * x) * y) := by
  unfold associator
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  abel

variable [IsAlternative M]

/-- The left alternative law, restated via the associator: `(x,x,y) = 0`. -/
theorem associator_self_left (x y : M) : associator x x y = 0 := by
  unfold associator
  rw [mul_alternative_left]
  abel

/-- The right alternative law, restated via the associator: `(y,x,x) = 0`. -/
theorem associator_right_self (x y : M) : associator y x x = 0 := by
  unfold associator
  rw [mul_alternative_right]
  abel

/-- Linearizing `associator_self_left` (`x ↦ x + z`) shows swapping the *first two* arguments of
the associator negates it. -/
theorem associator_swap_first (x y z : M) : associator x y z = -associator y x z := by
  have h : associator (x + y) (x + y) z = 0 := associator_self_left (x + y) z
  rw [associator_add_left, associator_add_mid, associator_add_mid,
    associator_self_left x z, associator_self_left y z] at h
  have h' : associator x y z + associator y x z = 0 := by
    abel_nf
    rw [zero_add, add_zero] at h
    exact h
  rw [eq_neg_iff_add_eq_zero]
  exact h'

/-- Linearizing `associator_right_self` (`x ↦ x + z`) shows swapping the *last two* arguments of
the associator negates it. -/
theorem associator_swap_last (x y z : M) : associator x y z = -associator x z y := by
  have h : associator x (y + z) (y + z) = 0 := associator_right_self (y + z) x
  rw [associator_add_mid, associator_add_right, associator_add_right,
    associator_right_self y x, associator_right_self z x] at h
  have h' : associator x y z + associator x z y = 0 := by
    rw [add_zero, zero_add] at h
    exact h
  rw [add_comm] at h'
  have h'' := neg_eq_iff_add_eq_zero.mpr h'
  exact h''.symm

/-- Swapping the *outer* two arguments of the associator also negates it -- the composite of
`associator_swap_first` and `associator_swap_last`, so the associator of any alternative ring is
alternating under all of `S₃`, not just the two adjacent transpositions built into the definition
of `IsAlternative`. -/
theorem associator_swap_outer (x y z : M) : associator x y z = -associator z y x := by
  rw [associator_swap_first, associator_swap_last y x z, associator_swap_first z y x]

/-- The associator is invariant under cyclic permutation of its arguments -- the composite of
`associator_swap_first` and `associator_swap_last` (each an odd permutation, so composing them
gives the even 3-cycle). -/
theorem associator_cyclic (x y z : M) : associator x y z = associator y z x := by
  rw [associator_swap_first x y z, associator_swap_last y x z, neg_neg]

/-- The associator vanishes when its *outer* two arguments agree (`(x,y,x) = 0`), the third of the
three "any two arguments equal" vanishing patterns -- alongside `associator_self_left` (first two
equal) and `associator_right_self` (last two equal). Immediate from `associator_swap_last` and
`associator_self_left`. -/
theorem associator_outer_self (x y : M) : associator x y x = 0 := by
  have h : associator x y x = -associator x x y := associator_swap_last x y x
  rw [associator_self_left] at h
  rw [h]; abel

/-- The flexible law: `x * (y * x) = (x * y) * x`, for any alternative (non-unital,
non-associative) ring. Follows from `associator_outer_self`, with no further hypotheses. -/
theorem mul_flexible (x y : M) : x * (y * x) = (x * y) * x := by
  have := associator_outer_self x y
  unfold associator at this
  rw [sub_eq_zero] at this
  exact this.symm

/-- A stepping stone toward the Left Bumping Formula / McCrimmon's key identity: the associator
`(x,y,x*x)` vanishes for any `x y` in an alternative ring, not just when the repeated argument sits
in an adjacent slot as the two basic alternative laws already say. -/
theorem associator_self_mul_self (x y : M) : associator x y (x * x) = 0 := by
  have h : x * (y * (x * x)) = (x * y) * (x * x) := by
    rw [← mul_alternative_right x y, mul_flexible x (y * x), mul_flexible x y,
      mul_alternative_right x (x * y)]
  unfold associator
  rw [h]; abel

/-- The mirror image of `associator_self_mul_self` under the left/right alternative laws: the
associator `(x*x,y,x)` also vanishes. -/
theorem associator_mul_self_self (x y : M) : associator (x * x) y x = 0 := by
  have h : (x * x) * (y * x) = ((x * x) * y) * x := by
    rw [← mul_alternative_left x (y * x), mul_flexible x y, mul_flexible x (x * y),
      mul_alternative_left x y]
  unfold associator
  rw [h]; abel

/-- The **left Moufang identity** (Schafer's (3.4)): `(x*(z*x))*y = x*(z*(x*y))`, where `x*(z*x) =
(x*z)*x` is the well-defined "sandwich" product `xzx` (unambiguous by `mul_flexible`). Proved by
reducing to `associator x (x*z) y + associator x (x*y) z = 0`, which splits (via
`associator_swap_last` twice) into two vanishing pairs: `associator (x*x) z y + associator (x*x) y
z = 0` and `associator x z y + associator x y z = 0`, both immediate from `associator_swap_last`.
-/
theorem moufang_left (x y z : M) : (x * (z * x)) * y = x * (z * (x * y)) := by
  rw [← sub_eq_zero]
  have hstart : (x * (z * x)) * y - x * (z * (x * y))
      = associator (x * z) x y + associator x z (x * y) := by
    rw [mul_flexible x z]
    unfold associator
    abel
  rw [hstart, associator_swap_first (x * z) x y, associator_swap_last x z (x * y)]
  have e1 : associator x (x * z) y = (x * x * z) * y - x * ((x * z) * y) := by
    unfold associator
    rw [mul_alternative_left]
  have e2 : associator x (x * y) z = (x * x * y) * z - x * ((x * y) * z) := by
    unfold associator
    rw [mul_alternative_left]
  rw [e1, e2]
  have lemA : associator (x * x) z y + associator (x * x) y z = 0 := by
    have := associator_swap_last (x * x) z y
    rw [this]; abel
  have lemB : associator x z y + associator x y z = 0 := by
    have := associator_swap_last x z y
    rw [this]; abel
  have e3 : (x * x * z) * y = associator (x * x) z y + (x * x) * (z * y) := by
    unfold associator; abel
  have e4 : (x * x * y) * z = associator (x * x) y z + (x * x) * (y * z) := by
    unfold associator; abel
  rw [e3, e4]
  have e5 : (x * x) * (z * y) = x * (x * (z * y)) := (mul_alternative_left x (z * y)).symm
  have e6 : (x * x) * (y * z) = x * (x * (y * z)) := (mul_alternative_left x (y * z)).symm
  rw [e5, e6]
  have key : -(x * (x * (z * y))) + x * ((x * z) * y) + (-(x * (x * (y * z))) + x * ((x * y) * z))
      = x * (associator x z y + associator x y z) := by
    unfold associator
    simp only [mul_add, mul_sub]
    abel
  rw [lemB, mul_zero] at key
  linear_combination (norm := abel) -lemA + key

/-- The **Left Bumping Formula** (McCrimmon): `[x,y,zx] = x[y,z,x]`, i.e. the associator
`(x,y,z*x)` equals `x` times the associator `(y,z,x)`. Derived from `moufang_left` plus
`associator_cyclic`: rewriting the last two arguments of `(x,y,zx)` via `associator_swap_last`
reduces the goal to `moufang_left`'s conclusion, and the final cancellation uses cyclic invariance
(`(y,z,x) = (z,x,y)`) rather than any new hypothesis. This is the key ingredient McCrimmon's
Jordan-identity proof of `H_3(D,-)` uses to collapse the "hard" off-diagonal cross-terms -- see
`JORDAN_IDENTITY_PLAN.md`. -/
theorem left_bumping (x y z : M) : associator x y (z * x) = x * associator y z x := by
  rw [← sub_eq_zero, associator_swap_last x y (z * x)]
  have e1 : associator x (z * x) y = x * (z * (x * y)) - x * ((z * x) * y) := by
    unfold associator
    rw [moufang_left]
  rw [e1]
  have cyc : associator y z x = associator z x y := associator_cyclic y z x
  have key : -(x * (z * (x * y)) - x * ((z * x) * y)) - x * associator y z x
      = x * (associator z x y - associator y z x) := by
    unfold associator
    simp only [mul_sub]
    abel
  rw [key, cyc, sub_self, mul_zero]

/-- The **linearization of the Left Bumping Formula**: linearize the repeated variable `p` in
`associator p q (r*p) = p * associator q r p` (`left_bumping`, with the roles renamed) via `p ↦
p+s`. Both "pure" terms (`p`-only and `s`-only) collapse via `left_bumping` itself, leaving this
bilinear cross-term identity -- the ingredient McCrimmon's key identity needs (see
`mccrimmon_key_identity` below) to handle terms where the outer multiplier and the associator's
repeated argument are *different* ring elements, not the same one as in `left_bumping`. -/
theorem left_bumping_linearized (p q r s : M) :
    associator s q (r * p) + associator p q (r * s)
      = s * associator q r p + p * associator q r s := by
  have h1 : associator (p + s) q (r * (p + s)) = (p + s) * associator q r (p + s) :=
    left_bumping (p + s) q r
  rw [mul_add] at h1
  rw [associator_add_right, associator_add_left, associator_add_left] at h1
  rw [associator_add_right, add_mul, mul_add, mul_add] at h1
  rw [left_bumping p q r, left_bumping s q r] at h1
  linear_combination (norm := abel) h1

/-- **McCrimmon's key identity** (*A Taste of Jordan Algebras*, (1.1.2)): `[w,[x,y,z]] = [w,x,yz] +
[w,y,zx] + [w,z,xy]`, i.e. the commutator of `w` with the associator `(x,y,z)` splits as a sum of
three associators, one for each way of multiplying two of `x,y,z` together and pairing with `w`.
Follows McCrimmon's own proof: rewrite `associator w x (y*z)` and `associator w z (x*y)` via
`associator_cyclic`/`associator_swap_last` into a form where `Teichmüller`'s identity applies to
two of the resulting associators at once; what's left after that cancels using
`left_bumping_linearized` and one more application of `associator_cyclic`. This is the identity
that ultimately collapses the "hard" off-diagonal cross-terms in the Albert-algebra Jordan-identity
proof -- see `JORDAN_IDENTITY_PLAN.md`. -/
theorem mccrimmon_key_identity (w x y z : M) :
    w * associator x y z - associator x y z * w
      = associator w x (y * z) + associator w y (z * x) + associator w z (x * y) := by
  have hcyc1 : associator w x (y * z) = associator x (y * z) w := associator_cyclic w x (y * z)
  have hcyc2 : associator w z (x * y) = -associator (x * y) z w := by
    have c1 : associator w z (x * y) = associator (x * y) w z := by
      rw [associator_cyclic w z (x * y), associator_cyclic z (x * y) w]
    rw [c1, associator_swap_last (x * y) w z]
  have teich := teichmuller x y z w
  have linLB := left_bumping_linearized x y z w
  have hcycfin : associator y z x = associator x y z := (associator_cyclic x y z).symm
  rw [hcyc1, hcyc2]
  linear_combination (norm := abel) teich - linLB - w * hcycfin

end IsAlternative
