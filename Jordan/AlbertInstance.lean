module

public import Jordan.AlbertAlgebra

/-!
# The Albert algebra as a `JordanAlgebra` instance

`Octonion.ofAlbert` is the Jordan algebra structure on `AlbertAlgebra`; it is a definition, not
an instance, because it needs the parameters `a`, `b`, `c` to be non-zero-divisors. Over a ring
without zero divisors that is just `a ≠ 0`, `b ≠ 0`, `c ≠ 0`, which instance search sees through
the `NeZero` class: `instJordanAlgebra`. With it, statements about the Albert algebra read like
those about the Hermitian matrix algebras, e.g. `isFormallyReal_of_signs :
IsFormallyReal R (AlbertAlgebra …)`.
-/

@[expose] public section

namespace Octonion

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R] {a b c : R}

omit [Invertible (2 : R)] [StarRing R] [TrivialStar R] in
/-- In a ring without zero divisors, a nonzero element is a non-zero-divisor, in the form
`ofAlbert` expects. -/
theorem eq_zero_of_mul_eq_zero_of_neZero [NoZeroDivisors R] (r : R) [NeZero r] :
    ∀ x : R, r * x = 0 → x = 0 :=
  fun _ hx => (mul_eq_zero.1 hx).resolve_left (NeZero.ne r)

/-- The Albert algebra is a Jordan algebra when `a`, `b`, `c` are nonzero in a ring without zero
divisors. -/
noncomputable instance instJordanAlgebra [NoZeroDivisors R] [NeZero a] [NeZero b] [NeZero c] :
    JordanAlgebra R (AlbertAlgebra (R := R) (a := a) (b := b) (c := c)) :=
  ofAlbert (eq_zero_of_mul_eq_zero_of_neZero a) (eq_zero_of_mul_eq_zero_of_neZero b)
    (eq_zero_of_mul_eq_zero_of_neZero c)

/-- The Albert algebra is formally real when `a < 0`, `b < 0` and `0 < c` (the octonions with
definite norm). -/
theorem isFormallyReal_of_signs [LinearOrder R] [IsStrictOrderedRing R] [NeZero a] [NeZero b]
    [NeZero c] (ha : a < 0) (hb : b < 0) (hc : 0 < c) :
    IsFormallyReal R (AlbertAlgebra (R := R) (a := a) (b := b) (c := c)) :=
  isFormallyReal (eq_zero_of_mul_eq_zero_of_neZero a) (eq_zero_of_mul_eq_zero_of_neZero b)
    (eq_zero_of_mul_eq_zero_of_neZero c) ha hb hc

end Octonion
