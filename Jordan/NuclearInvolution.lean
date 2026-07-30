import Jordan.Alternative
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Star.Basic

/-!
# Nuclear involutions

An involution `star` on a (possibly non-associative) ring `D` is *nuclear* if every symmetric
(star-fixed) element lies in the nucleus of `D` -- the set of elements that associate trivially,
in any slot, with any other two elements. This is the hypothesis McCrimmon's Matrix Associator
Facts (*A Taste of Jordan Algebras*, Appendix C.1, Lemma C.1.2) place on the coordinate algebra `D`
of `H_3(D,-)`, used there to make associators touching Hermitian-matrix diagonal entries vanish,
and to replace a lower-triangular entry `star x` by `-x` inside an associator. Both consequences
are proved here in fully generic form (`assoc_star_first/mid/last`), independent of any particular
matrix construction -- see `JORDAN_IDENTITY_PLAN.md`.
-/

open IsAlternative

variable {D : Type*} [NonUnitalNonAssocRing D] [IsAlternative D]

/-- `x` lies in the nucleus of `D`: it associates trivially in every slot, with any two other
elements. -/
def IsNuclear (x : D) : Prop :=
  ∀ y z : D, associator x y z = 0 ∧ associator y x z = 0 ∧ associator y z x = 0

omit [IsAlternative D] in
/-- A nuclear element slips into the first argument's left factor for free: `n[x,y,z] = [nx,y,z]`
(part of McCrimmon's Nuclear Slipping Formula 21.2.1(1)). Needs only `IsNuclear n`, no
involution -- a one-line consequence of `teichmuller` plus `IsNuclear`'s first clause, applied
three times to kill everything but the term we want. -/
theorem nuclear_slip_left {n : D} (hn : IsNuclear n) (x y z : D) :
    associator (n * x) y z = n * associator x y z := by
  have h := teichmuller n x y z
  rw [(hn (x * y) z).1, (hn x (y * z)).1, (hn x y).1, zero_mul] at h
  linear_combination (norm := abel) h

/-- The second-argument analogue of `nuclear_slip_left`, via `associator_swap_first` twice. -/
theorem nuclear_slip_mid {n : D} (hn : IsNuclear n) (x y z : D) :
    associator x (n * y) z = n * associator x y z := by
  rw [associator_swap_first x (n * y) z, nuclear_slip_left hn y x z,
    associator_swap_first y x z, mul_neg, neg_neg]

/-- The third-argument analogue of `nuclear_slip_left`, via `associator_swap_last` and
`nuclear_slip_mid`. -/
theorem nuclear_slip_last {n : D} (hn : IsNuclear n) (x y z : D) :
    associator x y (n * z) = n * associator x y z := by
  rw [associator_swap_last x y (n * z), nuclear_slip_mid hn x z y,
    associator_swap_last x z y, mul_neg, neg_neg]

omit [IsAlternative D] in
/-- The mirror of `nuclear_slip_last`: `n` slipped into the *right* factor of the last argument
instead of the left, giving `[x,y,z]n` rather than `n[x,y,z]` -- proved independently from
`teichmuller` plus `IsNuclear`'s third clause, exactly like `nuclear_slip_left`. -/
theorem nuclear_slip_last_right {n : D} (hn : IsNuclear n) (x y z : D) :
    associator x y (z * n) = associator x y z * n := by
  have h := teichmuller x y z n
  rw [(hn (x * y) z).2.2, (hn x (y * z)).2.2, (hn y z).2.2, mul_zero] at h
  linear_combination (norm := abel) h

variable [StarAddMonoid D]

/-- A **nuclear involution**: every symmetric (star-fixed) element of `D` lies in the nucleus, and
the nucleus is closed under commutators with arbitrary elements (McCrimmon's Alternative Nucleus
Lemma 21.2.1(2), `[N,D] ⊆ N`). The second field is, in general, *derivable* from the first alone
(via `Teichmüller` plus the swap/cyclic lemmas already in `Jordan.Alternative`, mirroring
McCrimmon's own proof "`n[x,y,z] = -n[y,x,z] = -[ny,x,z] = [x,ny,z] = [xn,y,z]`, subtracting the
last two gives `[[n,x],y,z]=0`") -- but that derivation is nontrivial, and a specific `D` may have
a much easier direct argument (e.g. `instOfAssociative` below), so it's kept as its own field
rather than forced through the general route. This is the ingredient the eventual **Nuclear
Slipping Formula** (`n` commutes with any associator value, McCrimmon 21.2.1(1)) needs -- see
`JORDAN_IDENTITY_PLAN.md`. -/
class IsNuclearInvolution (D : Type*) [NonUnitalNonAssocRing D] [IsAlternative D]
    [StarAddMonoid D] : Prop where
  isNuclear_of_star_eq : ∀ x : D, star x = x → IsNuclear x
  isNuclear_comm : ∀ n x : D, IsNuclear n → IsNuclear (n * x - x * n)

/-- Every associative ring, with any additive involution `star`, is trivially a nuclear
involution: associativity makes *every* element nuclear (the associator vanishes identically, no
`star`-fixedness needed at all), so both defining implications hold vacuously. This covers, e.g.,
`H_3(A,-)` for associative coordinate rings `A` (matrices over the reals, complexes, quaternions)
for free -- the genuinely new content of a nuclear involution only bites for non-associative `D`
such as the octonions. -/
instance instOfAssociative {D : Type*} [NonUnitalRing D] [StarAddMonoid D] :
    IsNuclearInvolution D where
  isNuclear_of_star_eq x _hx := fun y z =>
    ⟨by unfold associator; rw [mul_assoc]; abel,
     by unfold associator; rw [mul_assoc]; abel,
     by unfold associator; rw [mul_assoc]; abel⟩
  isNuclear_comm n x _hn := fun y z =>
    ⟨by unfold associator; rw [mul_assoc]; abel,
     by unfold associator; rw [mul_assoc]; abel,
     by unfold associator; rw [mul_assoc]; abel⟩

variable [IsNuclearInvolution D]

/-- Every trace `x + star x` is symmetric (automatic from `star` being additive and involutive),
hence nuclear by `IsNuclearInvolution`. -/
theorem isNuclear_add_star (x : D) : IsNuclear (x + star x) := by
  apply IsNuclearInvolution.isNuclear_of_star_eq
  rw [star_add, star_star, add_comm]

/-- Inside an associator, a `star`-ed first argument can be traded for minus the un-starred one --
the "replace `a_ji` by `-a_ij`" trick used throughout McCrimmon's Matrix Associator Facts proof. -/
theorem assoc_star_first (x y z : D) : associator (star x) y z = -associator x y z := by
  have h : associator (star x) y z + associator x y z = 0 := by
    rw [← associator_add_left, add_comm (star x) x]
    exact (isNuclear_add_star x y z).1
  linear_combination (norm := abel) h

/-- The middle-argument analogue of `assoc_star_first`. -/
theorem assoc_star_mid (x y z : D) : associator x (star y) z = -associator x y z := by
  have h : associator x (star y) z + associator x y z = 0 := by
    rw [← associator_add_mid, add_comm (star y) y]
    exact (isNuclear_add_star y x z).2.1
  linear_combination (norm := abel) h

/-- The last-argument analogue of `assoc_star_first`. -/
theorem assoc_star_last (x y z : D) : associator x y (star z) = -associator x y z := by
  have h : associator x y (star z) + associator x y z = 0 := by
    rw [← associator_add_right, add_comm (star z) z]
    exact (isNuclear_add_star z x y).2.2
  linear_combination (norm := abel) h

/-- **McCrimmon's Nuclear Slipping Formula** (21.2.1(1)), commutativity form: a nuclear element
commutes with *any* associator value. Follows from `nuclear_slip_last` (`n` slipped left into the
last argument) and `nuclear_slip_last_right` (`n` slipped right into the last argument) plus
`isNuclear_comm`: the difference `associator x y (n*z) - associator x y (z*n)` equals `associator x
y (n*z - z*n)`, which vanishes since `n*z - z*n` is nuclear (`isNuclear_comm`'s conclusion applied
with `z`) and hence kills any associator with it in the last slot. This is the ingredient
McCrimmon's `3x3` Coordinate Theorem C.1.3 (the Jordan identity for `H_3(D,-)`) needs to make a
diagonal (hence nuclear) matrix entry commute with an off-diagonal associator value -- see
`JORDAN_IDENTITY_PLAN.md`. -/
theorem nuclear_comm_associator {n : D} (hn : IsNuclear n) (x y z : D) :
    n * associator x y z = associator x y z * n := by
  have h4 := nuclear_slip_last hn x y z
  have h5 := nuclear_slip_last_right hn x y z
  have hzero : associator x y (n * z - z * n) = 0 :=
    (IsNuclearInvolution.isNuclear_comm n z hn x y).2.2
  have hsplit : associator x y (n * z) - associator x y (z * n) = associator x y (n * z - z * n) :=
    by unfold associator; simp only [mul_sub]; abel
  rw [hzero] at hsplit
  linear_combination (norm := abel) -h4 + h5 + hsplit
