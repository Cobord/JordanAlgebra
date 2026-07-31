import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

class JordanAlgebra (R : outParam (Type u)) (M : Type v) [CommRing R] extends
    NonAssocRing M, Module R M, IsScalarTower R M M, SMulCommClass R M M where
  jordan_mul_comm : ∀ x y : M, x * y = y * x
  jordan_identity : ∀ x y : M, x * x * (x * y) = x * (x * x * y)

/-- Any commutative ring is trivially a Jordan algebra over itself, via its own (associative)
multiplication: commutativity is `mul_comm`, and the Jordan identity holds for *any* associative
product (commutative or not) by `mul_assoc` alone. This is the degenerate "`1 x 1` Hermitian
matrix" case that the `n x n` constructions (`RealQM`, `ComplexQM`, `QuaternionicQM`, and the
self-adjoint elements of `Octonion`) all collapse to when `n = 1`. -/
instance JordanAlgebra.ofCommRing (R : Type*) [CommRing R] : JordanAlgebra R R where
  jordan_mul_comm := mul_comm
  jordan_identity x y := by rw [mul_assoc, mul_assoc]

namespace JordanAlgebra

variable {R M : Type*} [CommRing R] [JordanAlgebra R M]

local notation "L" => AddMonoid.End.mulLeft
local notation "Rm" => AddMonoid.End.mulRight

private abbrev twoSmulEnd (f : AddMonoid.End M) : AddMonoid.End M :=
  SMul.smul (2 : R) f

private theorem twoSmulEnd_eq_add (f : AddMonoid.End M) : twoSmulEnd f = f + f := by
  apply AddMonoidHom.ext
  intro x
  change (2 : R) • f x = f x + f x
  rw [two_smul R]

private theorem twoSmulEnd_add (f g : AddMonoid.End M) :
    twoSmulEnd (f + g) = twoSmulEnd f + twoSmulEnd g := by
  rw [twoSmulEnd_eq_add, twoSmulEnd_eq_add, twoSmulEnd_eq_add]
  abel

/-- In a commutative Jordan algebra, left and right multiplication by the same element commute. -/
theorem lmul_comm_rmul (a b : M) : a * b * a = a * (b * a) := by
  rw [jordan_mul_comm (a * b) a, jordan_mul_comm b a]

/-- The Jordan identity as commutation of left multiplication by `a` and by `a * a`. -/
theorem lmul_lmul_comm_lmul (a b : M) : a * a * (a * b) = a * (a * a * b) :=
  jordan_identity a b

/-- A right-handed form of the Jordan identity. -/
theorem lmul_lmul_comm_rmul (a b : M) : a * a * (b * a) = a * a * b * a := by
  rw [jordan_mul_comm b a, jordan_identity, jordan_mul_comm]

/-- Another commutative form of the Jordan identity. -/
theorem lmul_comm_rmul_rmul (a b : M) : a * b * (a * a) = a * (b * (a * a)) := by
  rw [jordan_mul_comm (a * b) (a * a), jordan_identity, jordan_mul_comm b (a * a)]

/-- Right multiplications by `a` and by `a * a` commute. -/
theorem rmul_comm_rmul_rmul (a b : M) : b * a * (a * a) = b * (a * a) * a := by
  rw [jordan_mul_comm b a, lmul_comm_rmul_rmul, jordan_mul_comm]

@[simp]
theorem commute_lmul_rmul (a : M) : Commute (L a) (Rm a) :=
  AddMonoidHom.ext fun _ => (lmul_comm_rmul _ _).symm

@[simp]
theorem commute_lmul_lmul_sq (a : M) : Commute (L a) (L (a * a)) :=
  AddMonoidHom.ext fun _ => (lmul_lmul_comm_lmul _ _).symm

@[simp]
theorem commute_lmul_rmul_sq (a : M) : Commute (L a) (Rm (a * a)) :=
  AddMonoidHom.ext fun _ => (lmul_comm_rmul_rmul _ _).symm

@[simp]
theorem commute_lmul_sq_rmul (a : M) : Commute (L (a * a)) (Rm a) :=
  AddMonoidHom.ext fun _ => lmul_lmul_comm_rmul _ _

@[simp]
theorem commute_rmul_rmul_sq (a : M) : Commute (Rm a) (Rm (a * a)) :=
  AddMonoidHom.ext fun _ => (rmul_comm_rmul_rmul _ _).symm

attribute [local instance 100] LieRing.ofAssociativeRing

theorem two_smul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add (a b : M) :
    twoSmulEnd (⁅L a, L (a * b)⁆ + ⁅L b, L (b * a)⁆) =
      ⁅L (a * a), L b⁆ + ⁅L (b * b), L a⁆ := by
  suffices twoSmulEnd ⁅L a, L (a * b)⁆ + twoSmulEnd ⁅L b, L (b * a)⁆ +
      ⁅L b, L (a * a)⁆ + ⁅L a, L (b * b)⁆ = 0 by
    rw [← sub_eq_zero, ← sub_sub, sub_eq_add_neg, sub_eq_add_neg, lie_skew, lie_skew,
      twoSmulEnd_add]
    exact this
  convert! (commute_lmul_lmul_sq (a + b)).lie_eq using 1
  simp only [add_mul, mul_add, map_add, lie_add, add_lie,
    (commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq, zero_add, add_zero]
  rw [twoSmulEnd_eq_add, twoSmulEnd_eq_add]
  rw [jordan_mul_comm b a]
  abel

private theorem linearization_aux0 {a b c : M} :
    ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ =
      ⁅L a + L b + L c,
        L (a * a) + L (b * b) + L (c * c) +
          twoSmulEnd (L (a * b)) + twoSmulEnd (L (c * a)) + twoSmulEnd (L (b * c))⁆ := by
  rw [add_mul, add_mul]
  iterate 6 rw [mul_add]
  iterate 10 rw [map_add]
  rw [jordan_mul_comm b a, jordan_mul_comm c a, jordan_mul_comm c b]
  iterate 3 rw [twoSmulEnd_eq_add]
  simp only [add_lie]
  abel_nf

private theorem linearization_aux1 {a b c : M} :
    ⁅L a + L b + L c,
        L (a * a) + L (b * b) + L (c * c) +
          twoSmulEnd (L (a * b)) + twoSmulEnd (L (c * a)) + twoSmulEnd (L (b * c))⁆ =
      ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
        ⁅L a, twoSmulEnd (L (a * b))⁆ + ⁅L a, twoSmulEnd (L (c * a))⁆ +
          ⁅L a, twoSmulEnd (L (b * c))⁆ +
        (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
          ⁅L b, twoSmulEnd (L (a * b))⁆ + ⁅L b, twoSmulEnd (L (c * a))⁆ +
            ⁅L b, twoSmulEnd (L (b * c))⁆) +
        (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
          ⁅L c, twoSmulEnd (L (a * b))⁆ + ⁅L c, twoSmulEnd (L (c * a))⁆ +
            ⁅L c, twoSmulEnd (L (b * c))⁆) := by
  rw [add_lie, add_lie]
  iterate 15 rw [lie_add]

private theorem linearization_aux2 {a b c : M} :
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
        ⁅L a, twoSmulEnd (L (a * b))⁆ + ⁅L a, twoSmulEnd (L (c * a))⁆ +
          ⁅L a, twoSmulEnd (L (b * c))⁆ +
        (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
          ⁅L b, twoSmulEnd (L (a * b))⁆ + ⁅L b, twoSmulEnd (L (c * a))⁆ +
            ⁅L b, twoSmulEnd (L (b * c))⁆) +
        (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
          ⁅L c, twoSmulEnd (L (a * b))⁆ + ⁅L c, twoSmulEnd (L (c * a))⁆ +
            ⁅L c, twoSmulEnd (L (b * c))⁆) =
      ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ +
        twoSmulEnd (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
        (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ +
          twoSmulEnd (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
        (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ +
          twoSmulEnd (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
        (twoSmulEnd ⁅L a, L (b * c)⁆ + twoSmulEnd ⁅L b, L (c * a)⁆ +
          twoSmulEnd ⁅L c, L (a * b)⁆) := by
  rw [(commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq,
    (commute_lmul_lmul_sq c).lie_eq, zero_add, add_zero, add_zero]
  simp only [twoSmulEnd_eq_add, lie_add]
  abel_nf

private theorem linearization_aux3 {a b c : M} :
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ +
        twoSmulEnd (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
        (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ +
          twoSmulEnd (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
        (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ +
          twoSmulEnd (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
        (twoSmulEnd ⁅L a, L (b * c)⁆ + twoSmulEnd ⁅L b, L (c * a)⁆ +
          twoSmulEnd ⁅L c, L (a * b)⁆) =
      twoSmulEnd ⁅L a, L (b * c)⁆ + twoSmulEnd ⁅L b, L (c * a)⁆ +
        twoSmulEnd ⁅L c, L (a * b)⁆ := by
  rw [add_eq_right]
  nth_rw 2 [jordan_mul_comm a b]
  nth_rw 1 [jordan_mul_comm c a]
  nth_rw 2 [jordan_mul_comm b c]
  iterate 3 rw [two_smul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add]
  iterate 2 rw [← lie_skew (L (a * a)), ← lie_skew (L (b * b)), ← lie_skew (L (c * c))]
  abel

theorem two_smul_lie_lmul_lmul_add_add_eq_zero (a b c : M) :
    twoSmulEnd (⁅L a, L (b * c)⁆ + ⁅L b, L (c * a)⁆ + ⁅L c, L (a * b)⁆) = 0 := by
  symm
  calc
    0 = ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ := by
      rw [(commute_lmul_lmul_sq (a + b + c)).lie_eq]
    _ = _ := by
      rw [linearization_aux0, linearization_aux1, linearization_aux2, linearization_aux3,
        twoSmulEnd_add, twoSmulEnd_add]

private theorem eq_zero_of_two_smul_eq_zero [Invertible (2 : R)] {f : AddMonoid.End M}
    (hf : twoSmulEnd f = 0) : f = 0 := by
  apply AddMonoidHom.ext
  intro x
  have hxEnd := congr_arg (fun g : AddMonoid.End M => g x) hf
  have hx : (2 : R) • f x = 0 := by
    rw [← AddMonoid.End.smul_apply (2 : R) f x]
    exact hxEnd
  calc
    f x = (1 : R) • f x := (one_smul R (f x)).symm
    _ = (⅟(2 : R) * 2) • f x := by rw [invOf_mul_self]
    _ = ⅟(2 : R) • ((2 : R) • f x) := by rw [smul_smul]
    _ = 0 := by rw [hx, smul_zero]

theorem lie_lmul_lmul_add_add_eq_zero [Invertible (2 : R)] (a b c : M) :
    ⁅L a, L (b * c)⁆ + ⁅L b, L (c * a)⁆ + ⁅L c, L (a * b)⁆ = 0 :=
  eq_zero_of_two_smul_eq_zero (two_smul_lie_lmul_lmul_add_add_eq_zero a b c)

theorem commute_lmul_mul_of_commute [Invertible (2 : R)] {a b c : M}
    (hb : Commute (L b) (L (c * a))) (hc : Commute (L c) (L (a * b))) :
    Commute (L a) (L (b * c)) := by
  rw [commute_iff_lie_eq]
  simpa [hb.lie_eq, hc.lie_eq] using lie_lmul_lmul_add_add_eq_zero a b c

theorem commute_lmul_mul_of_commute_left [Invertible (2 : R)] {a b c : M}
    (ha : Commute (L a) (L (b * c))) (hc : Commute (L c) (L (a * b))) :
    Commute (L b) (L (c * a)) := by
  rw [commute_iff_lie_eq]
  have h := lie_lmul_lmul_add_add_eq_zero a b c
  rw [ha.lie_eq, hc.lie_eq] at h
  simpa using h

theorem commute_lmul_mul_of_commute_right [Invertible (2 : R)] {a b c : M}
    (ha : Commute (L a) (L (b * c))) (hb : Commute (L b) (L (c * a))) :
    Commute (L c) (L (a * b)) := by
  rw [commute_iff_lie_eq]
  have h := lie_lmul_lmul_add_add_eq_zero a b c
  rw [ha.lie_eq, hb.lie_eq] at h
  simpa using h

theorem commute_lmul_mul_self_of_commute_sq [Invertible (2 : R)] {a b : M}
    (h : Commute (L b) (L (a * a))) :
    Commute (L a) (L (a * b)) := by
  rw [commute_iff_lie_eq]
  apply eq_zero_of_two_smul_eq_zero
  rw [twoSmulEnd_eq_add]
  have hlin := lie_lmul_lmul_add_add_eq_zero a a b
  rw [h.lie_eq] at hlin
  simpa [jordan_mul_comm b a] using hlin

theorem commute_lmul_sq_of_commute_mul_self [Invertible (2 : R)] {a b : M}
    (h : Commute (L a) (L (a * b))) :
    Commute (L b) (L (a * a)) := by
  rw [commute_iff_lie_eq]
  have hlin := lie_lmul_lmul_add_add_eq_zero a a b
  rw [jordan_mul_comm b a, h.lie_eq] at hlin
  simpa using hlin

theorem commute_lmul_mul_self_iff_commute_sq [Invertible (2 : R)] (a b : M) :
    Commute (L a) (L (a * b)) ↔ Commute (L b) (L (a * a)) :=
  ⟨commute_lmul_sq_of_commute_mul_self, commute_lmul_mul_self_of_commute_sq⟩

/-- The Jordan powers of `x`, with the usual convention `x ^[0] = 1`, `x ^[n+1] = x * x ^[n]`. -/
def jordanPow (x : M) : ℕ → M
  | 0 => 1
  | n + 1 => x * jordanPow x n

@[simp] theorem jordanPow_zero (x : M) : jordanPow x 0 = 1 := rfl

theorem jordanPow_succ (x : M) (n : ℕ) : jordanPow x (n + 1) = x * jordanPow x n := rfl

@[simp] theorem jordanPow_one (x : M) : jordanPow x 1 = x := by
  rw [jordanPow_succ, jordanPow_zero, mul_one]

theorem jordanPow_two (x : M) : jordanPow x 2 = x * x := by
  rw [jordanPow_succ, jordanPow_one]

theorem commute_lmul_jordanPow_two (x : M) : Commute (L x) (L (jordanPow x 2)) := by
  rw [jordanPow_two]
  exact commute_lmul_lmul_sq x

theorem jordanPow_three (x : M) : jordanPow x 3 = x * (x * x) := by
  rw [jordanPow_succ, jordanPow_two]

theorem commute_lmul_jordanPow_succ_of_commute_sq [Invertible (2 : R)] {x : M} {n : ℕ}
    (h : Commute (L (jordanPow x n)) (L (x * x))) :
    Commute (L x) (L (jordanPow x (n + 1))) := by
  rw [jordanPow_succ]
  exact commute_lmul_mul_self_of_commute_sq h

theorem commute_sq_of_commute_lmul_jordanPow_succ [Invertible (2 : R)] {x : M} {n : ℕ}
    (h : Commute (L x) (L (jordanPow x (n + 1)))) :
    Commute (L (jordanPow x n)) (L (x * x)) := by
  rw [jordanPow_succ] at h
  exact commute_lmul_sq_of_commute_mul_self h

theorem commute_lmul_jordanPow_succ_iff_commute_sq [Invertible (2 : R)] (x : M) (n : ℕ) :
    Commute (L x) (L (jordanPow x (n + 1))) ↔
      Commute (L (jordanPow x n)) (L (x * x)) :=
  ⟨commute_sq_of_commute_lmul_jordanPow_succ, commute_lmul_jordanPow_succ_of_commute_sq⟩

theorem commute_lmul_jordanPow_three [Invertible (2 : R)] (x : M) :
    Commute (L x) (L (jordanPow x 3)) := by
  rw [jordanPow_three]
  exact commute_lmul_mul_self_of_commute_sq (Commute.refl (L (x * x)))

private theorem eq_of_add_self_eq_add_self [Invertible (2 : R)] {v w : M}
    (h : v + v = w + w) : v = w := by
  have h2 : (2 : R) • v = (2 : R) • w := by rw [two_smul, two_smul]; exact h
  calc
    v = (1 : R) • v := (one_smul R v).symm
    _ = (⅟(2 : R) * 2) • v := by rw [invOf_mul_self]
    _ = ⅟(2 : R) • ((2 : R) • v) := by rw [smul_smul]
    _ = ⅟(2 : R) • ((2 : R) • w) := by rw [h2]
    _ = (⅟(2 : R) * 2) • w := by rw [smul_smul]
    _ = (1 : R) • w := by rw [invOf_mul_self]
    _ = w := one_smul R w

private theorem sq_rmul_add_expand (x z y : M) :
    (x + z) * (x + z) * y * (x + z) - (x + z) * (x + z) * (y * (x + z)) =
      (x * x * y * x - x * x * (y * x)) + (z * z * y * z - z * z * (y * z))
        + (x * x * y * z - x * x * (y * z)) + (z * z * y * x - z * z * (y * x))
        + ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x)))
        + ((x * z * y * z - x * z * (y * z)) + (x * z * y * z - x * z * (y * z))) := by
  have hxx : (x + z) * (x + z) = x * x + z * z + (x * z + x * z) := by
    rw [add_mul, mul_add, mul_add, jordan_mul_comm z x]; abel
  rw [hxx]
  simp only [add_mul, mul_add]
  abel

private theorem sq_rmul_sub_expand (x z y : M) :
    (x - z) * (x - z) * y * (x - z) - (x - z) * (x - z) * (y * (x - z)) =
      (x * x * y * x - x * x * (y * x)) - (z * z * y * z - z * z * (y * z))
        - (x * x * y * z - x * x * (y * z)) + (z * z * y * x - z * z * (y * x))
        - ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x)))
        + ((x * z * y * z - x * z * (y * z)) + (x * z * y * z - x * z * (y * z))) := by
  have hxx : (x - z) * (x - z) = x * x + z * z - (x * z + x * z) := by
    rw [sub_mul, mul_sub, mul_sub, jordan_mul_comm z x]; abel
  rw [hxx]
  simp only [sub_mul, mul_sub, add_mul]
  abel

/-- McCrimmon's (JAX2'): the quadratic-in-`x` linearization of the Jordan identity in the form
`lmul_lmul_comm_rmul` (`[x², y, x] = 0`), obtained by substituting `x ↦ x + z` and `x ↦ x - z`
and combining (see *A Taste of Jordan Algebras*, Linearization Proposition 1.8.5). -/
private theorem jax2_prime [Invertible (2 : R)] (x y z : M) :
    (x * x * y * z - x * x * (y * z)) +
      ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x))) = 0 := by
  have hx : x * x * y * x - x * x * (y * x) = 0 := sub_eq_zero_of_eq (lmul_lmul_comm_rmul x y).symm
  have hz : z * z * y * z - z * z * (y * z) = 0 := sub_eq_zero_of_eq (lmul_lmul_comm_rmul z y).symm
  have hAdd : (x + z) * (x + z) * y * (x + z) - (x + z) * (x + z) * (y * (x + z)) = 0 :=
    sub_eq_zero_of_eq (lmul_lmul_comm_rmul (x + z) y).symm
  have hSub : (x - z) * (x - z) * y * (x - z) - (x - z) * (x - z) * (y * (x - z)) = 0 :=
    sub_eq_zero_of_eq (lmul_lmul_comm_rmul (x - z) y).symm
  rw [sq_rmul_add_expand] at hAdd
  rw [sq_rmul_sub_expand] at hSub
  simp only [hx, hz, zero_add, add_zero, zero_sub, sub_zero] at hAdd hSub
  apply eq_of_add_self_eq_add_self (w := 0)
  rw [add_zero]
  have hcomb : (x * x * y * z - x * x * (y * z)) +
        ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x))) +
      ((x * x * y * z - x * x * (y * z)) +
        ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x)))) =
      ((x * x * y * z - x * x * (y * z)) + (z * z * y * x - z * z * (y * x)) +
          ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x))) +
          ((x * z * y * z - x * z * (y * z)) + (x * z * y * z - x * z * (y * z)))) -
        (-(x * x * y * z - x * x * (y * z)) + (z * z * y * x - z * z * (y * x)) -
            ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x))) +
            ((x * z * y * z - x * z * (y * z)) + (x * z * y * z - x * z * (y * z)))) := by
    abel
  rw [hcomb, hAdd, hSub, sub_zero]

private theorem jax2_prime_add_expand (x w y z : M) :
    ((x + w) * (x + w) * y * z - (x + w) * (x + w) * (y * z)) +
        ((((x + w) * z) * y * (x + w) - (x + w) * z * (y * (x + w))) +
          (((x + w) * z) * y * (x + w) - (x + w) * z * (y * (x + w)))) =
      ((x * x * y * z - x * x * (y * z)) +
          ((x * z * y * x - x * z * (y * x)) + (x * z * y * x - x * z * (y * x))))
        + ((w * w * y * z - w * w * (y * z)) +
          ((w * z * y * w - w * z * (y * w)) + (w * z * y * w - w * z * (y * w))))
        + ((((x * w) * y * z - (x * w) * (y * z)) + ((x * w) * y * z - (x * w) * (y * z)))
          + (((x * z) * y * w - (x * z) * (y * w)) + ((x * z) * y * w - (x * z) * (y * w)))
          + (((w * z) * y * x - (w * z) * (y * x)) + ((w * z) * y * x - (w * z) * (y * x)))) := by
  have hxw : (x + w) * (x + w) = x * x + w * w + (x * w + x * w) := by
    rw [add_mul, mul_add, mul_add, jordan_mul_comm w x]; abel
  have hxwz : (x + w) * z = x * z + w * z := add_mul x w z
  rw [hxw, hxwz]
  simp only [add_mul, mul_add]
  abel

/-- McCrimmon's (JAX2''): the fully linearized (multilinear) Jordan identity, obtained by
linearizing (JAX2') (`jax2_prime`) a second time in `x`, via `x ↦ x + w` (see *A Taste of
Jordan Algebras*, Linearization Proposition 1.8.5). -/
private theorem jax2_double_prime [Invertible (2 : R)] (x w y z : M) :
    ((x * w) * y * z - (x * w) * (y * z)) +
      (((x * z) * y * w - (x * z) * (y * w)) + ((w * z) * y * x - (w * z) * (y * x))) = 0 := by
  have h1 := jax2_prime (x + w) y z
  have h2 := jax2_prime x y z
  have h3 := jax2_prime w y z
  have hexp := jax2_prime_add_expand x w y z
  rw [h1, h2, h3, zero_add, zero_add] at hexp
  apply eq_of_add_self_eq_add_self (w := 0)
  rw [add_zero]
  linear_combination (norm := abel) -hexp

/-- Linearized fundamental formula: left multiplication by the triple product `(b * d) * c`
expressed as a combination of compositions of `L b`, `L c`, `L d`. -/
theorem lmul_mul_mul_eq [Invertible (2 : R)] (b c d : M) :
    L ((b * d) * c) =
      L (b * d) * L c + L (c * d) * L b + L (b * c) * L d
        - L b * L c * L d - L d * L c * L b := by
  ext z
  show (b * d) * c * z =
      (b * d) * (c * z) + (c * d) * (b * z) + (b * c) * (d * z)
        - b * (c * (d * z)) - d * (c * (b * z))
  have hjdp := jax2_double_prime b d c z
  have e1 : b * z * c * d = d * (c * (b * z)) := by
    rw [jordan_mul_comm (b * z) c, jordan_mul_comm (c * (b * z)) d]
  have e2 : b * z * (c * d) = c * d * (b * z) := jordan_mul_comm (b * z) (c * d)
  have e3 : d * z * c * b = b * (c * (d * z)) := by
    rw [jordan_mul_comm (d * z) c, jordan_mul_comm (c * (d * z)) b]
  have e4 : d * z * (c * b) = b * c * (d * z) := by
    rw [jordan_mul_comm c b, jordan_mul_comm (d * z) (b * c)]
  linear_combination (norm := abel) hjdp - e1 + e2 - e3 + e4

theorem jordanPow_mul_self_eq_succ (a : M) (k : ℕ) :
    jordanPow a k * a = jordanPow a (k + 1) := by
  rw [jordanPow_succ, jordan_mul_comm]

theorem jordanPow_mul_self_mul_self_eq_succ_succ (a : M) (k : ℕ) :
    (jordanPow a k * a) * a = jordanPow a (k + 2) := by
  rw [jordanPow_mul_self_eq_succ, jordanPow_mul_self_eq_succ]

/-- Specialization of `lmul_mul_mul_eq` at `b := jordanPow a k`, `c := d := a`. -/
theorem lmul_jordanPow_succ_succ [Invertible (2 : R)] (a : M) (k : ℕ) :
    L (jordanPow a (k + 2)) =
      L (jordanPow a (k + 1)) * L a + L (a * a) * L (jordanPow a k) +
        L (jordanPow a (k + 1)) * L a
        - L (jordanPow a k) * L a * L a - L a * L a * L (jordanPow a k) := by
  have h := lmul_mul_mul_eq (jordanPow a k) a a
  rwa [jordanPow_mul_self_mul_self_eq_succ_succ, jordanPow_mul_self_eq_succ] at h

/-- `L (a ^[k])` lies in the (commutative, since `L a` and `L (a * a)` commute) subring generated
by `L a` and `L (a * a)` -- i.e. it is a polynomial in those two commuting operators. -/
theorem lmul_jordanPow_mem_closure [Invertible (2 : R)] (a : M) (k : ℕ) :
    L (jordanPow a k) ∈ Subring.closure ({L a, L (a * a)} : Set (AddMonoid.End M)) := by
  have hLa : L a ∈ Subring.closure ({L a, L (a * a)} : Set (AddMonoid.End M)) :=
    Subring.subset_closure (Set.mem_insert _ _)
  have hLsq : L (a * a) ∈ Subring.closure ({L a, L (a * a)} : Set (AddMonoid.End M)) :=
    Subring.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))
  suffices h : ∀ k, L (jordanPow a k) ∈ Subring.closure ({L a, L (a * a)} : Set (AddMonoid.End M)) ∧
      L (jordanPow a (k + 1)) ∈ Subring.closure ({L a, L (a * a)} : Set (AddMonoid.End M)) from
    (h k).1
  intro k
  induction k with
  | zero =>
    refine ⟨?_, by rwa [jordanPow_one]⟩
    rw [jordanPow_zero, show L (1 : M) = 1 from AddMonoidHom.ext fun x => one_mul x]
    exact Subring.one_mem _
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [lmul_jordanPow_succ_succ]
    exact Subring.sub_mem _
      (Subring.sub_mem _
        (Subring.add_mem _ (Subring.add_mem _ (Subring.mul_mem _ ih.2 hLa) (Subring.mul_mem _ hLsq ih.1))
          (Subring.mul_mem _ ih.2 hLa))
        (Subring.mul_mem _ (Subring.mul_mem _ ih.1 hLa) hLa))
      (Subring.mul_mem _ (Subring.mul_mem _ hLa hLa) ih.1)

/-- If a set `s` in a ring pairwise commutes (i.e. `s ⊆ centralizer s`), then any two elements of
the subring it generates commute with each other. -/
theorem Subring.commute_of_mem_closure_of_subset_centralizer {N : Type*} [Ring N] {s : Set N}
    (hs : s ⊆ Subring.centralizer s) {a b : N} (ha : a ∈ Subring.closure s)
    (hb : b ∈ Subring.closure s) : Commute a b := by
  have h1 : Subring.closure s ≤ Subring.centralizer s :=
    le_trans (Subring.closure_le_centralizer_centralizer s) (Subring.centralizer_le _ _ hs)
  have h2 : Subring.closure s ≤ Subring.centralizer (Subring.closure s) :=
    le_trans (Subring.closure_le_centralizer_centralizer s) (Subring.centralizer_le _ _ h1)
  exact (Subring.mem_centralizer_iff.mp (h2 ha) b hb).symm

theorem commute_lmul_jordanPow_mn [Invertible (2 : R)] (x : M) (m n : ℕ) :
  Commute (L (jordanPow x m)) (L (jordanPow x n)) := by
  refine Subring.commute_of_mem_closure_of_subset_centralizer ?_
    (lmul_jordanPow_mem_closure x m) (lmul_jordanPow_mem_closure x n)
  rintro f (rfl | rfl) g (rfl | rfl) <;>
    first
      | exact Commute.refl _
      | exact commute_lmul_lmul_sq x
      | exact (commute_lmul_lmul_sq x).symm

theorem jordanPow_mn [Invertible (2 : R)] (x y : M) (m n : ℕ) :
  (jordanPow x m) * ((jordanPow x n) * y) =
  (jordanPow x n) * ((jordanPow x m) * y) := by
  change (L (jordanPow x m)) ((L (jordanPow x n)) y) = (L (jordanPow x n)) ((L (jordanPow x m)) y)
  have mn_commute := commute_lmul_jordanPow_mn x m n
  simpa using congrFun (congrArg DFunLike.coe mn_commute) y

section SumSqCone

/-- The cone of sums of squares in a Jordan algebra `M`: `IsSumSq` (equivalently, membership in
`AddSubmonoid.sumSq M`) makes sense for `M` itself, since it only needs `Mul`/`Add`/`Zero`, which
`M` has via its `NonAssocRing` structure. -/
abbrev sumSqCone (R M : Type*) [CommRing R] [JordanAlgebra R M] : AddSubmonoid M :=
  AddSubmonoid.sumSq M

/-- The cone of sums of squares is closed under addition: this is automatic, since
`AddSubmonoid.sumSq M` is literally an additive submonoid (`IsSumSq.add` underneath). -/
theorem add_mem_sumSqCone {s t : M} (hs : s ∈ sumSqCone R M) (ht : t ∈ sumSqCone R M) :
    s + t ∈ sumSqCone R M :=
  add_mem hs ht

/-- The cone of sums of squares is also closed under scaling by squares of scalars: for `r : R`,
`(r * r) • (x * x) = (r • x) * (r • x)` is again a square (using the Jordan algebra's module
structure relating `R` and `M`, i.e. `IsScalarTower`/`SMulCommClass`), so scaling a sum of squares
by `r * r` produces another sum of squares. Together with closure under addition, this is what
makes the sums of squares a genuine *cone* rather than just an additive submonoid. -/
theorem smul_sq_mem_sumSqCone {s : M} (hs : s ∈ sumSqCone R M) (r : R) :
    (r * r) • s ∈ sumSqCone R M := by
  induction hs with
  | zero => simp
  | sq_add x _ ih =>
    rw [smul_add, show (r * r) • (x * x) = (r • x) * (r • x) by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]]
    exact (IsSumSq.mul_self (r • x)).add ih

end SumSqCone

end JordanAlgebra

namespace HermitianJordan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [StarRing A] [Invertible (2 : R)]

/-- The self-adjoint ("Hermitian") elements of a star algebra `A` over `R`, given that the
scalars coming from `R` are themselves fixed by the involution. -/
def hermitian (hR : ∀ r : R, star (algebraMap R A r) = algebraMap R A r) : Submodule R A where
  carrier := {x | star x = x}
  zero_mem' := star_zero A
  add_mem' hx hy := by
    show star (_ + _) = _ + _
    rw [star_add, hx, hy]
  smul_mem' r x hx := by
    show star (r • x) = r • x
    rw [Algebra.smul_def, star_mul, hx, hR]
    exact (Algebra.commutes r x).symm

variable (hR : ∀ r : R, star (algebraMap R A r) = algebraMap R A r)

omit [Invertible (2 : R)] in
theorem symm_sq_mem (x y : hermitian hR) :
    star (x.1 * y.1 + y.1 * x.1) = x.1 * y.1 + y.1 * x.1 := by
  have hx : star x.1 = x.1 := x.2
  have hy : star y.1 = y.1 := y.2
  rw [star_add, star_mul, star_mul, hx, hy, add_comm]

omit [StarRing A] in
private theorem assoc_jordan_identity (x y : A) :
    (x * x + x * x) * (x * y + y * x) + (x * y + y * x) * (x * x + x * x) =
    x * ((x * x + x * x) * y + y * (x * x + x * x)) +
      ((x * x + x * x) * y + y * (x * x + x * x)) * x := by
  noncomm_ring

instance : Mul (hermitian hR) where
  mul x y := ⟨(⅟2 : R) • (x.1 * y.1 + y.1 * x.1), (hermitian hR).smul_mem _ (symm_sq_mem hR x y)⟩

theorem mul_def (x y : hermitian hR) :
    (x * y).1 = (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) := rfl

/-- The Jordan product of a Hermitian element with itself is just ordinary squaring: the halving
in `mul_def` cancels against the doubled term `x.1 * x.1 + x.1 * x.1`. -/
theorem mul_self_eq (x : hermitian hR) : (x * x).1 = x.1 * x.1 := by
  rw [mul_def, ← two_smul R, smul_smul, invOf_mul_self, one_smul]

theorem hermitian_mul_comm (x y : hermitian hR) : x * y = y * x := by
  apply Subtype.ext
  rw [mul_def, mul_def, add_comm]

instance : NonAssocSemiring (hermitian hR) where
  left_distrib x y z := by
    apply Subtype.ext
    show (⅟2 : R) • (x.1 * (y.1 + z.1) + (y.1 + z.1) * x.1) =
        (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) + (⅟2 : R) • (x.1 * z.1 + z.1 * x.1)
    simp only [mul_add, add_mul, ← smul_add]
    congr 1
    abel
  right_distrib x y z := by
    apply Subtype.ext
    show (⅟2 : R) • ((x.1 + y.1) * z.1 + z.1 * (x.1 + y.1)) =
        (⅟2 : R) • (x.1 * z.1 + z.1 * x.1) + (⅟2 : R) • (y.1 * z.1 + z.1 * y.1)
    simp only [mul_add, add_mul, ← smul_add]
    congr 1
    abel
  zero_mul x := by
    apply Subtype.ext
    show (⅟2 : R) • ((0 : A) * x.1 + x.1 * 0) = (0 : A)
    simp
  mul_zero x := by
    apply Subtype.ext
    show (⅟2 : R) • (x.1 * (0 : A) + 0 * x.1) = (0 : A)
    simp
  one := ⟨1, star_one A⟩
  one_mul x := by
    apply Subtype.ext
    show (⅟2 : R) • ((1 : A) * x.1 + x.1 * 1) = x.1
    rw [one_mul, mul_one, ← two_smul R, smul_smul, invOf_mul_self, one_smul]
  mul_one x := by
    apply Subtype.ext
    show (⅟2 : R) • (x.1 * (1 : A) + 1 * x.1) = x.1
    rw [mul_one, one_mul, ← two_smul R, smul_smul, invOf_mul_self, one_smul]

instance : NonAssocRing (hermitian hR) :=
  { (inferInstance : NonAssocSemiring (hermitian hR)),
    (inferInstance : AddCommGroup (hermitian hR)) with }

instance : IsScalarTower R (hermitian hR) (hermitian hR) where
  smul_assoc r x y := by
    apply Subtype.ext
    simp only [smul_eq_mul, mul_def, Submodule.coe_smul_of_tower]
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_smul, smul_smul, mul_comm r]

instance : SMulCommClass R (hermitian hR) (hermitian hR) where
  smul_comm r x y := by
    apply Subtype.ext
    simp only [smul_eq_mul, mul_def, Submodule.coe_smul_of_tower]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, smul_smul, mul_comm r]

/-- Given an associative `R`-algebra `A` with an involution (a `StarRing` structure, possibly
the identity) and `2` invertible in `R`, the Hermitian elements of `A` form a Jordan algebra
under the symmetrized product `x ∘ y = (xy + yx) / 2`. -/
instance ofInvolutiveAlgebra : JordanAlgebra R (hermitian hR) :=
  { (inferInstance : NonAssocRing (hermitian hR)),
    (inferInstance : Module R (hermitian hR)),
    (inferInstance : IsScalarTower R (hermitian hR) (hermitian hR)),
    (inferInstance : SMulCommClass R (hermitian hR) (hermitian hR)) with
    jordan_mul_comm := hermitian_mul_comm hR
    jordan_identity := fun x y => by
      apply Subtype.ext
      show (⅟2 : R) • ((⅟2 : R) • (x.1 * x.1 + x.1 * x.1) * ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1)) +
            (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) * ((⅟2 : R) • (x.1 * x.1 + x.1 * x.1))) =
          (⅟2 : R) • (x.1 * ((⅟2 : R) • ((⅟2 : R) • (x.1 * x.1 + x.1 * x.1) * y.1 +
              y.1 * ((⅟2 : R) • (x.1 * x.1 + x.1 * x.1)))) +
            (⅟2 : R) • ((⅟2 : R) • (x.1 * x.1 + x.1 * x.1) * y.1 +
              y.1 * ((⅟2 : R) • (x.1 * x.1 + x.1 * x.1))) * x.1)
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← smul_add]
      rw [assoc_jordan_identity] }

end HermitianJordan
