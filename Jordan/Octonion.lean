import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Unique
import Jordan.RealQM

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

/-- Cayley-Dickson multiplication:
`(p, q) * (r, s) = (p * r - c • (star s * q), s * p + q * star r)`. -/
instance : Mul (Octonion R a b c) where
  mul x y := mk (x.1 * y.1 - c • (star y.2 * x.2)) (y.2 * x.1 + x.2 * star y.1)

@[simp] theorem mul_fst (x y : Octonion R a b c) :
    (x * y).1 = x.1 * y.1 - c • (star y.2 * x.2) := rfl
@[simp] theorem mul_snd (x y : Octonion R a b c) :
    (x * y).2 = y.2 * x.1 + x.2 * star y.1 := rfl

/-- Cayley-Dickson conjugation: `star (p, q) = (star p, -q)`. -/
instance : Star (Octonion R a b c) where
  star x := mk (star x.1) (-x.2)

@[simp] theorem star_fst (x : Octonion R a b c) : (star x).1 = star x.1 := rfl
@[simp] theorem star_snd (x : Octonion R a b c) : (star x).2 = -x.2 := rfl

instance : One (Octonion R a b c) := ⟨mk 1 0⟩

@[simp] theorem one_fst : (1 : Octonion R a b c).1 = 1 := rfl
@[simp] theorem one_snd : (1 : Octonion R a b c).2 = 0 := rfl

instance : NonAssocRing (Octonion R a b c) where
  left_distrib x y z := by ext <;> simp [mul_add] <;> ring
  right_distrib x y z := by ext <;> simp [add_mul] <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

/-- Cayley-Dickson conjugation is an involutive anti-automorphism, exactly as for `ℍ` (it never
needs `2` invertible): `star (x * y) = star y * star x`. -/
instance : StarRing (Octonion R a b c) where
  star_involutive x := by apply Octonion.ext <;> simp
  star_add x y := by apply Octonion.ext <;> simp [add_comm]
  star_mul x y := by apply Octonion.ext <;> simp

/-! ### Alternativity

The classical fact that makes Cayley-Dickson doubling of an *associative* algebra (here `ℍ`)
produce an *alternative* one: `x * (x * y) = (x * x) * y` and `(y * x) * x = y * (x * x)`. The key
inputs, both about `ℍ` alone, are that the "trace" `p + star p` and "norm" `star q * q = q * star
q` of any quaternion are central scalars (`R`-multiples of `1`, commuting with everything) -- this
is what survives associativity getting lost in the doubling. -/

section Alternative

/-- The trace `p + star p` of a quaternion is a central scalar. -/
theorem add_star_eq_coe (p : ℍ[R, a, 0, b]) : p + star p = ((2 * p.re : R) : ℍ[R, a, 0, b]) := by
  simpa using QuaternionAlgebra.self_add_star (c₂ := (0 : R)) p

theorem add_star_mul_comm (p q : ℍ[R, a, 0, b]) : (p + star p) * q = q * (p + star p) := by
  rw [add_star_eq_coe]; exact QuaternionAlgebra.coe_commutes _ q

/-- The norm `star q * q` of a quaternion is a central scalar, and agrees with `q * star q`. -/
theorem star_mul_self_eq_coe (q : ℍ[R, a, 0, b]) :
    star q * q = ((star q * q).re : R) := QuaternionAlgebra.star_mul_eq_coe q

theorem star_mul_self_mul_comm (p q : ℍ[R, a, 0, b]) :
    (star q * q) * p = p * (star q * q) := by
  rw [star_mul_self_eq_coe]; exact QuaternionAlgebra.coe_commutes _ p

theorem mul_star_self_eq_star_mul_self (q : ℍ[R, a, 0, b]) : q * star q = star q * q :=
  (star_comm_self' q).symm

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

/-! ### The `1 x 1` self-adjoint case

The self-adjoint ("Hermitian") elements of `Octonion R a b c` are exactly the scalars: with `2`
invertible, `star x = x` forces every octonion-imaginary coordinate of `x` to vanish, i.e. `x.2 =
0` and `x.1` itself has no quaternion-imaginary part either. This is the degenerate `n = 1` case
of the (here unbuilt, since octonions are non-associative beyond `n = 3`) Hermitian-octonionic-
matrix construction, and it agrees with the `n = 1` case of `RealQM`. -/

section SelfAdjointOne

variable [Invertible (2 : R)]

theorem eq_zero_of_neg_eq_self {N : Type*} [AddCommGroup N] [Module R N] {z : N} (hz : -z = z) :
    z = 0 := by
  have h2 : (2 : R) • z = 0 := by
    rw [two_smul, add_eq_zero_iff_eq_neg]; exact hz.symm
  simpa [smul_smul] using congrArg (⅟(2 : R) • ·) h2

/-- The scalar embedding `R → Octonion R a b c`: the `1 x 1` case of a Hermitian-matrix
construction, where there are no off-diagonal entries to speak of. -/
def scalarEmbed : R →+* Octonion R a b c where
  toFun r := mk (algebraMap R ℍ[R, a, 0, b] r) 0
  map_one' := by apply Octonion.ext <;> simp
  map_mul' _ _ := by apply Octonion.ext <;> simp
  map_zero' := by apply Octonion.ext <;> simp
  map_add' _ _ := by apply Octonion.ext <;> simp

omit [Invertible (2 : R)] in
@[simp] theorem scalarEmbed_fst (r : R) :
    (scalarEmbed r : Octonion R a b c).1 = algebraMap R ℍ[R, a, 0, b] r := rfl

omit [Invertible (2 : R)] in
@[simp] theorem scalarEmbed_snd (r : R) : (scalarEmbed r : Octonion R a b c).2 = 0 := rfl

omit [Invertible (2 : R)] in
theorem scalarEmbed_injective :
    Function.Injective (scalarEmbed (R := R) (a := a) (b := b) (c := c)) := by
  intro r s h
  exact QuaternionAlgebra.algebraMap_injective (congrArg Prod.fst h)

omit [Invertible (2 : R)] in
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

end SelfAdjointOne

end Octonion

section OctonionMatrices

variable {R : Type*}
  [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
  [IsAddTorsionFree R]
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

omit [IsAddTorsionFree R] [Fintype n] [DecidableEq n] in
lemma diag_real
  (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
  (i : n) :
    ∃ r : R, M.val i i = Octonion.scalarEmbed r := by
  have h := congrArg (fun M => M i i) M.property
  exact (Octonion.isSelfAdjoint_iff (M.val i i)).mp h

omit i2 [StarRing R] [TrivialStar R] [IsAddTorsionFree R] in
lemma diag_just_11 (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.re = r := by
  intro h
  simp [h]
omit i2 [StarRing R] [TrivialStar R] [IsAddTorsionFree R] in
lemma diag_no_1i (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imI = 0 := by
  intro h
  simp [h]
omit i2 [StarRing R] [TrivialStar R] [IsAddTorsionFree R] in
lemma diag_no_1j (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imJ = 0 := by
  intro h
  simp [h]
omit i2 [StarRing R] [TrivialStar R] [IsAddTorsionFree R] in
lemma diag_no_1k (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imK = 0 := by
  intro h
  simp [h]
omit i2 [StarRing R] [TrivialStar R] [IsAddTorsionFree R] in
lemma diag_no_2 (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.2 = 0 := by
  intro h
  simp [h]

omit i2 [StarRing R] [TrivialStar R] [IsAddTorsionFree R] in
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

instance CommRing_HermitianOctonionMatrixOne : NonAssocCommRing (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
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

end OctonionMatrices

namespace Octonion

/-! ### Comparison with `RealQM`'s `1 x 1` case

`RealQM.symmetricMatrices R (Fin 1)` collapses to plain `R` too (`RealQM.oneRingEquiv`), since a
`1 x 1` matrix is trivially symmetric and the symmetrized product agrees with ordinary
multiplication once there's only one entry. Composing that with `Octonion.scalarEmbed` gives an
explicit embedding of `RealQM`'s `1 x 1` Jordan algebra into the octonions, landing exactly on the
self-adjoint elements: both constructions are literally the same copy of `R`. -/
section OneByOne

variable {R : Type*}
variable [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
  [IsAddTorsionFree R]
variable {a b c : R}

omit [IsAddTorsionFree R] in
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

omit i2 [IsAddTorsionFree R] in
private lemma HermitianOctonionMatrixOne.add_re
    (M N : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1)) :
    (((M + N).val 0 0).1.re : R) = (M.val 0 0).1.re + (N.val 0 0).1.re := by
  rfl

omit [IsAddTorsionFree R] in
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

The `2 x 2` construction is the spin-factor case: a Hermitian matrix has two scalar diagonal
entries and one octonionic off-diagonal entry, with the opposite off-diagonal entry forced by
conjugate symmetry. The intended comparison theorem here is an explicit `≃+*`, parallel to
`ofSymmetricMatricesOne`, but with the appropriate `SpinFactor` as the target instead of the
`1 x 1` scalar algebra. -/
section TwoByTwo

/- TODO: Construct the explicit `≃+*` between `2 x 2` Hermitian octonionic matrices and the
appropriate `SpinFactor`, with the off-diagonal octonion providing the vector part and the two
diagonal scalars providing the spin-factor scalar coordinates. -/

end TwoByTwo

/-! ### The `3 x 3` Hermitian octonionic case

The `3 x 3` construction is the exceptional Hermitian octonionic Jordan algebra. It uses the same
ambient matrix type and symmetrized product, but no associative matrix algebra is assumed: all
identities here must be proved from the non-associative octonion multiplication and the Hermitian
closure of `⅟2 • (AB + BA)`. -/
section ThreeByThree

/- TODO: Develop the `3 x 3` Hermitian octonionic Jordan algebra. This is the exceptional case, so
the main work is proving the Jordan identities directly for the symmetrized product without relying
on associativity of octonion matrix multiplication. -/

end ThreeByThree

end Octonion
