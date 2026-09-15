import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Non-associative division algebras

A *division algebra* over a commutative ring `R` is a unital, not necessarily associative
`R`-algebra in which multiplication by any nonzero element, on either side, is a bijection. Mathlib's
`DivisionRing` is the associative case; there is no class for the general notion, which is the one
the octonions and the algebras cut out of a `Triality` satisfy.

Following `JordanAlgebra`, the class bundles the underlying algebra structure (`NonAssocRing`,
`Module R`, and the two compatibility classes) together with `NoZeroDivisors` and `Nontrivial`,
which any division algebra satisfies. `NoZeroDivisors` is in fact a consequence of the bijectivity
axioms; `DivisionAlgebra.ofBijective` derives it for you.
-/

/-- A unital, not necessarily associative division algebra over `R`: multiplication by a nonzero
element on either side is bijective. -/
class DivisionAlgebra (R : outParam (Type u)) (K : Type v) [CommRing R] extends
    NonAssocRing K, Module R K, IsScalarTower R K K, SMulCommClass R K K,
    NoZeroDivisors K, Nontrivial K where
  mul_left_bijective : ∀ {a : K}, a ≠ 0 → Function.Bijective (a * ·)
  mul_right_bijective : ∀ {b : K}, b ≠ 0 → Function.Bijective (· * b)

namespace DivisionAlgebra

variable {R : Type u} {K : Type v} [CommRing R]

/-- Build a division algebra from bijectivity of the two multiplications; the absence of zero
divisors follows (if `a ≠ 0` then `a * ·` is injective and kills `0`, so `a * b = 0` forces
`b = 0`). -/
abbrev ofBijective [NonAssocRing K] [Module R K] [IsScalarTower R K K] [SMulCommClass R K K]
    [Nontrivial K]
    (hl : ∀ {a : K}, a ≠ 0 → Function.Bijective (a * ·))
    (hr : ∀ {b : K}, b ≠ 0 → Function.Bijective (· * b)) : DivisionAlgebra R K where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr ((hl ha).1 (h.trans (mul_zero a).symm))
  mul_left_bijective := hl
  mul_right_bijective := hr

/-- An associative division ring that is an `R`-algebra is a division algebra: multiplication by
a nonzero element is the bijection `Equiv.mulLeft₀`/`Equiv.mulRight₀`. Not an instance, since
`R` is an `outParam` of `DivisionAlgebra` and is not determined by `K`; see `ofField` for the
case `R = K`. -/
abbrev ofDivisionRing (R : Type u) [CommRing R] [DivisionRing K] [Algebra R K] :
    DivisionAlgebra R K :=
  ofBijective (fun {a} ha => (Equiv.mulLeft₀ a ha).bijective)
    (fun {b} hb => (Equiv.mulRight₀ b hb).bijective)

/-- A field is a division algebra over itself (cf. `JordanAlgebra.ofCommRing`). Low priority so it
never shadows a bespoke `DivisionAlgebra` instance. -/
instance (priority := 100) ofField (K : Type u) [Field K] : DivisionAlgebra K K :=
  ofDivisionRing K

variable [DivisionAlgebra R K]

theorem mul_left_injective {a : K} (ha : a ≠ 0) : Function.Injective (a * ·) :=
  (mul_left_bijective (R := R) ha).1

theorem mul_left_surjective {a : K} (ha : a ≠ 0) : Function.Surjective (a * ·) :=
  (mul_left_bijective (R := R) ha).2

theorem mul_right_injective {b : K} (hb : b ≠ 0) : Function.Injective (· * b) :=
  (mul_right_bijective (R := R) hb).1

theorem mul_right_surjective {b : K} (hb : b ≠ 0) : Function.Surjective (· * b) :=
  (mul_right_bijective (R := R) hb).2

/-- Every equation `a * x = c` with `a ≠ 0` has a unique solution. -/
theorem existsUnique_mul_left_eq {a : K} (ha : a ≠ 0) (c : K) : ∃! x, a * x = c :=
  (mul_left_bijective (R := R) ha).existsUnique c

/-- Every equation `x * b = c` with `b ≠ 0` has a unique solution. -/
theorem existsUnique_mul_right_eq {b : K} (hb : b ≠ 0) (c : K) : ∃! x, x * b = c :=
  (mul_right_bijective (R := R) hb).existsUnique c

end DivisionAlgebra
