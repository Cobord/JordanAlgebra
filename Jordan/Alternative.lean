import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

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

/-- The flexible law: `x * (y * x) = (x * y) * x`, for any alternative (non-unital,
non-associative) ring. Follows from `associator_self_left x y = 0` and `associator_swap_last x y
x`, with no further hypotheses. -/
theorem mul_flexible (x y : M) : x * (y * x) = (x * y) * x := by
  have h : associator x y x = -associator x x y := associator_swap_last x y x
  rw [associator_self_left] at h
  have h0 : associator x y x = 0 := by rw [h]; abel
  have := h0
  unfold associator at this
  rw [sub_eq_zero] at this
  exact this.symm

end IsAlternative
