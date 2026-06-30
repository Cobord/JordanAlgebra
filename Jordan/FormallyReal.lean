import Jordan.JordanAlgebra
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Algebra.Ring.Semireal.Defs

/-- Mathlib's inductively-defined `IsSumSq` agrees with "is a `Fintype`-indexed sum of squares".
The class `IsFormallyReal` itself still needs the explicit indexed family (it must track that
*each* summand vanishes, which `IsSumSq` alone forgets), but every "is/isn't *some* sum of
squares" statement downstream is stated using Mathlib's `IsSumSq`/`IsSemireal` instead of
reinventing the existential. -/
theorem isSumSq_iff_exists_sum_mul_self {R : Type*} [AddCommMonoid R] [Mul R] {s : R} :
    IsSumSq s ↔ ∃ (ι : Type) (_ : Fintype ι) (x : ι → R), s = ∑ i, x i * x i := by
  constructor
  · intro hs
    induction hs with
    | zero => exact ⟨PEmpty, inferInstance, PEmpty.elim, by simp⟩
    | sq_add a _ ih =>
      obtain ⟨ι, hι, x, hx⟩ := ih
      refine ⟨Option ι, inferInstance, fun i => i.elim a x, ?_⟩
      rw [Fintype.sum_option]
      simp [hx]
  · rintro ⟨ι, hι, x, rfl⟩
    exact IsSumSq.sum_mul_self Finset.univ x

/-- Ring homomorphisms preserve sums of squares. -/
theorem IsSumSq.map {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {s : R} (hs : IsSumSq s) : IsSumSq (f s) := by
  induction hs with
  | zero => simp [IsSumSq.zero]
  | sq_add a _ ih => simpa using IsSumSq.sq_add (f a) ih

/-!
# Formally real Jordan algebras

A Jordan algebra `M` over `R` is *formally real* if a sum of squares can only vanish trivially:
`x 1 * x 1 + ⋯ + x k * x k = 0` forces every `x i = 0`. This is the algebraic condition underlying
the classification of finite-dimensional formally real Jordan algebras (the
`RealQM`/`ComplexQM`/`QuaternionicQM`/`SpinFactor`/`Octonion` families).

Note this is *weaker* than asking some bilinear form to be positive definite: positive
definiteness needs an order on `R` (to make sense of `B x x > 0`) and so is only available when
`R` already carries one (e.g. `R = ℝ`), whereas "sum of squares zero implies all summands zero" is
a condition purely internal to the algebra `M`, stateable -- and meaningful to ask about -- for a
Jordan algebra over *any* commutative ring `R`.
-/

/-- A Jordan algebra is formally real if a sum of squares `x 1 * x 1 + ⋯ + x k * x k` can only be
zero when every `x i` is zero. -/
class IsFormallyReal (R M : Type*) [CommRing R] [JordanAlgebra R M] : Prop where
  protected eq_zero_of_sum_mul_self_eq_zero :
    ∀ {ι : Type} [Fintype ι] (x : ι → M), (∑ i, x i * x i = 0) → ∀ i, x i = 0

/-- A *generic trace and determinant* of rank `n` on a formally real Jordan algebra `M`: a linear
trace form `trace` (degree `1`) and a degree-`n` homogeneous determinant form `det`, normalized so
that `trace 1 = n` and `det 1 = 1` (as for the identity element of an `n x n` matrix algebra).

This does *not* yet record the full classical "generic minimal polynomial" identity
`x^[n] - T₁(x) • x^[n - 1] + ⋯ ± Tₙ(x) • 1 = 0` -- that needs all `n` of the intermediate trace
forms `T₂, ..., T_{n - 1}` (of which `trace = T₁` and `det = Tₙ` are only the two endpoints), and
none of those intermediate forms are constructed here. What's recorded is the data classically
known to exist for the formally real examples in this project (e.g. `SpinFactor`, rank `2`), kept
deliberately minimal until more of the intermediate structure is needed. -/
structure IsFormallyRealDetTrace (R M : Type*) [CommRing R] [JordanAlgebra R M]
    [IsFormallyReal R M] where
  /-- The rank: the degree of the determinant form (and the value of the trace at `1`). -/
  rank : ℕ
  /-- The (linear, degree `1`) generic trace form. -/
  trace : M →ₗ[R] R
  /-- The (degree-`rank` homogeneous) generic determinant form. -/
  det : M → R
  det_smul : ∀ (r : R) (x : M), det (r • x) = r ^ rank • det x
  trace_one : trace 1 = (rank : R)
  det_one : det 1 = 1

namespace IsFormallyRealDetTrace

variable {R M : Type*} [CommRing R] [JordanAlgebra R M] [IsFormallyReal R M]

/-- The *state space*: the base of the cone of squares cut out by `trace x = 1`, e.g. the density
matrices (positive semidefinite, trace `1`) in the classical `n x n` Hermitian-matrix case. -/
def states (dt : IsFormallyRealDetTrace R M) : Set M :=
  {x : M | x ∈ JordanAlgebra.sumSqCone R M ∧ dt.trace x = 1}

/-- The *pure states*: the states that are also idempotent. Classically, a trace-`1` idempotent
in a rank-`n` Euclidean Jordan algebra is exactly a rank-`1` (primitive) idempotent, i.e. a rank-`1`
projection -- the extreme points of the state space, e.g. the pure quantum states `|ψ⟩⟨ψ|` among
the density matrices in the classical `n x n` Hermitian-matrix case. -/
def pureStates (dt : IsFormallyRealDetTrace R M) : Set M :=
  {x : M | x ∈ dt.states ∧ x * x = x}

/-- The expectation value of an observable in a state `s ∈ dt.states`: `trace (s * a)`, using the
Jordan product (e.g. `tr(ρ ∘ A)` for a density matrix `ρ` and Hermitian observable `A` in the
classical case). Linear in the observable `a`, since `trace` is linear and the Jordan product is
bilinear. -/
def expect (dt : IsFormallyRealDetTrace R M) (s : dt.states) : M →ₗ[R] R where
  toFun a := dt.trace ((s : M) * a)
  map_add' a b := by rw [mul_add, map_add]
  map_smul' r a := by simp [mul_smul_comm]

@[simp] theorem expect_apply (dt : IsFormallyRealDetTrace R M) (s : dt.states) (a : M) :
    dt.expect s a = dt.trace ((s : M) * a) := rfl

/-- The state space is convex in the "squares" sense that generalizes `0 ≤ t ≤ 1`-convexity to a
ring without an order: for weights `r, s : R` with `r * r + s * s = 1` (in place of `t` and
`1 - t` for `t = r * r ∈ [0, 1]`), a "square-weighted" combination of two states is again a state.
-/
theorem sq_smul_add_sq_smul_mem_states (dt : IsFormallyRealDetTrace R M)
    {state1 state2 : M} (h1 : state1 ∈ dt.states) (h2 : state2 ∈ dt.states)
    {r s : R} (hrs : r * r + s * s = 1) :
    (r * r) • state1 + (s * s) • state2 ∈ dt.states := by
  obtain ⟨hsq1, htr1⟩ := h1
  obtain ⟨hsq2, htr2⟩ := h2
  refine ⟨JordanAlgebra.add_mem_sumSqCone (JordanAlgebra.smul_sq_mem_sumSqCone hsq1 r)
    (JordanAlgebra.smul_sq_mem_sumSqCone hsq2 s), ?_⟩
  rw [map_add, map_smul, map_smul, htr1, htr2, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hrs]

/-- The expectation value of an observable in a "square-weighted" combination of two states is
the corresponding combination of the individual expectation values -- the Jordan-algebraic analogue
of `E_{t ρ₁ + (1-t) ρ₂}[A] = t E_{ρ₁}[A] + (1-t) E_{ρ₂}[A]`. -/
theorem expect_sq_smul_add_sq_smul (dt : IsFormallyRealDetTrace R M)
    {state1 state2 : M} (h1 : state1 ∈ dt.states) (h2 : state2 ∈ dt.states)
    {r s : R} (hrs : r * r + s * s = 1) (a : M) :
    dt.expect ⟨(r * r) • state1 + (s * s) • state2, dt.sq_smul_add_sq_smul_mem_states h1 h2 hrs⟩
        a =
      (r * r) * dt.expect ⟨state1, h1⟩ a + (s * s) * dt.expect ⟨state2, h2⟩ a := by
  simp only [expect_apply, add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul]

end IsFormallyRealDetTrace

namespace IsFormallyReal

variable {R M : Type*} [CommRing R] [JordanAlgebra R M] [IsFormallyReal R M]

theorem eq_zero_of_mul_self_eq_zero {x : M} (hx : x * x = 0) : x = 0 := by
  have h := IsFormallyReal.eq_zero_of_sum_mul_self_eq_zero (ι := PUnit) (fun _ => x)
    (by simpa [one_nsmul] using hx)
  exact h PUnit.unit

omit [IsFormallyReal R M] in
theorem not_of_exists_mul_self_eq_zero {x : M} (hx : x ≠ 0) (hsq : x * x = 0) :
    ¬ IsFormallyReal R M := by
  intro hFR
  letI : IsFormallyReal R M := hFR
  exact hx (eq_zero_of_mul_self_eq_zero hsq)

omit [IsFormallyReal R M] in
theorem not_of_neg_one_eq_sum_squares [Nontrivial M] (hsq : IsSumSq (-1 : R)) :
    ¬ IsFormallyReal R M := by
  obtain ⟨ι, hι, x, hsq⟩ := isSumSq_iff_exists_sum_mul_self.mp hsq
  letI : Fintype ι := hι
  intro hFR
  letI : IsFormallyReal R M := hFR
  let y : Option ι → M
    | none => 1
    | some i => x i • (1 : M)
  have hy : ∑ i, y i * y i = 0 := by
    simp only [y, Fintype.sum_option, one_mul]
    simp_rw [smul_mul_assoc, one_mul]
    simp_rw [smul_smul]
    change 1 + ∑ i, (x i * x i) • (1 : M) = 0
    rw [← Finset.sum_smul]
    rw [← hsq, neg_one_smul, add_neg_cancel]
  have hzero := IsFormallyReal.eq_zero_of_sum_mul_self_eq_zero
    (R := R) (M := M) (ι := Option ι) y hy none
  exact one_ne_zero hzero

/-- A nontrivial formally real Jordan algebra forces its *scalar ring* `R` to be Artin–Schreier
formally real too: `-1` can't be a sum of squares in `R`. This is the direction that actually
matters -- the Jordan algebra is what justifies caring about this ring-level condition on `R` at
all (e.g. it's what lets us rule out `R` admitting an injective ring hom from any `ℤ_[p]`, since
`-1` *is* a sum of squares there); it isn't an independently-motivated simplification of
`IsFormallyReal`, it's a *consequence* of it. -/
theorem neg_one_not_sum_squares [Nontrivial M] : IsSemireal R :=
  IsSemireal.of_not_isSumSq_neg_one
    (fun hsq => not_of_neg_one_eq_sum_squares hsq ‹IsFormallyReal R M›)

theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {x : M} (hx : n • x = 0) :
    x = 0 := by
  have hsum : ∑ _ : Fin n, x * x = 0 := by
    have hm := congrArg (fun y : M => (AddMonoid.End.mulRight x) y) hx
    rw [map_nsmul] at hm
    rw [show (AddMonoid.End.mulRight x) x = x * x by rfl, map_zero] at hm
    simpa [Finset.sum_const] using hm
  exact IsFormallyReal.eq_zero_of_sum_mul_self_eq_zero (fun _ : Fin n => x) hsum
    ⟨0, Nat.pos_of_ne_zero hn⟩

theorem isAddTorsionFree : IsAddTorsionFree M where
  nsmul_right_injective {n} hn := by
    intro x y hxy
    change n • x = n • y at hxy
    rw [← sub_eq_zero]
    apply eq_zero_of_nsmul_eq_zero hn
    rw [nsmul_sub]
    rw [hxy, sub_self]

theorem charZero_of_nontrivial [Nontrivial M] : CharZero M := by
  letI : IsAddTorsionFree M := isAddTorsionFree (R := R) (M := M)
  refine charZero_of_inj_zero ?_
  intro n hn
  by_contra hn0
  exact one_ne_zero (eq_zero_of_nsmul_eq_zero hn0 (by
    rw [Nat.smul_one_eq_cast (R := M)]
    exact hn))

theorem charZero_of_nontrivial_scalar [Nontrivial M] : CharZero R := by
  letI : CharZero M := charZero_of_nontrivial (R := R) (M := M)
  exact CharZero.of_module M

end IsFormallyReal

/-- If *some* nontrivial Jordan algebra over `R` is formally real, then `R` itself is
Artin–Schreier formally real: `-1` is not a sum of squares in `R`. (The converse -- that an
Artin–Schreier formally real `R` admits *some* formally real Jordan algebra over it -- is also
true, but the Jordan algebra is the primary notion for this file, so only this direction is
recorded here.) -/
theorem neg_one_not_sum_squares_of_isFormallyReal {R : Type*} [CommRing R]
    (h : ∃ (M : Type*) (_ : JordanAlgebra R M) (_ : Nontrivial M), IsFormallyReal R M) :
    IsSemireal R := by
  obtain ⟨M, hJA, hNT, hFR⟩ := h
  letI := hJA
  letI := hNT
  letI := hFR
  exact IsFormallyReal.neg_one_not_sum_squares (R := R) (M := M)

namespace PadicInt

open Polynomial IsLocalRing

theorem toZMod_natCast_val {p : ℕ} [Fact p.Prime] (y : ZMod p) :
    PadicInt.toZMod ((y.val : ℕ) : ℤ_[p]) = y := by
  apply ZMod.val_injective
  rw [PadicInt.val_toZMod_eq_zmodRepr, PadicInt.zmodRepr_natCast_of_lt]
  exact y.val_lt

/-- If `a ≠ 0` in `ZMod p` and `a * a + b * b = -1`, Hensel's lemma (applied to `X ^ 2 + (w * w + 1)`
at the lift of `a`, with `w` any lift of `b`) produces `z w : ℤ_[p]` with `z * z + w * w = -1`. -/
private theorem hensel_sq_add_const_of_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : ZMod p} (ha : a ≠ 0) (hab : a * a + b * b = -1) :
    ∃ z w : ℤ_[p], z * z + w * w = -1 := by
  let w : ℤ_[p] := (b.val : ℕ)
  let a0 : ℤ_[p] := (a.val : ℕ)
  let f : ℤ_[p][X] := X ^ 2 + C (w * w + 1)
  have hwcast : PadicInt.toZMod w = b := PadicInt.toZMod_natCast_val b
  have hacast : PadicInt.toZMod a0 = a := PadicInt.toZMod_natCast_val a
  have hf : f.Monic := by
    simpa [f] using
      (Polynomial.monic_X_pow_add_C (R := ℤ_[p]) (a := w * w + 1) (n := 2) (by norm_num))
  have heval : f.eval a0 ∈ maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    have : a * a + (b * b + 1) = 0 := by linear_combination hab
    simp [f, a0, w, pow_two, this]
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal ℤ_[p]) (f.derivative.eval a0)) := by
    letI : Field (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) := Ideal.Quotient.field (maximalIdeal ℤ_[p])
    rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    intro hmem
    have hker : PadicInt.toZMod (f.derivative.eval a0) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      exact hmem
    have htwo : (2 : ZMod p) ≠ 0 :=
      (NeZero.of_not_dvd (R := ZMod p) (p := p) (n := 2)
        (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : Nat.Prime p) Nat.prime_two).mp h))).out
    have htwo' : (1 + 1 : ZMod p) ≠ 0 := by
      simpa [show (1 + 1 : ZMod p) = (2 : ZMod p) by norm_num] using htwo
    simp [f, a0, w, ha, htwo'] at hker
  rcases HenselianRing.is_henselian f hf a0 heval hderiv with ⟨z, hz, _⟩
  refine ⟨z, w, ?_⟩
  have : z * z + (w * w + 1) = 0 := by simpa [f, IsRoot.def, pow_two] using hz
  linear_combination this

/-- For `a * a + b * b = -1` in `ZMod p` (`p` odd), Hensel's lemma produces `z w : ℤ_[p]` with
`z * z + w * w = -1`. Unlike `hensel_sq_add_const_of_ne_zero`, no nonvanishing hypothesis is
needed: since `a = b = 0` would give `0 = -1`, one of `a`, `b` is automatically nonzero, and we
dispatch to whichever side that is. -/
private theorem hensel_sq_add_const {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : ZMod p} (hab : a * a + b * b = -1) :
    ∃ z w : ℤ_[p], z * z + w * w = -1 := by
  rcases eq_or_ne a 0 with ha0 | ha0
  · have hb0 : b ≠ 0 := by
      rintro rfl
      rw [ha0] at hab
      simp at hab
    obtain ⟨z, w, hzw⟩ := hensel_sq_add_const_of_ne_zero hp2 hb0 (a := b) (b := a)
      (by linear_combination hab)
    exact ⟨z, w, hzw⟩
  · exact hensel_sq_add_const_of_ne_zero hp2 ha0 hab

/-- `-1` is a sum of (two) squares in `ℤ_[p]` for any odd prime `p` -- no splitting on `p % 4`
needed, since `ZMod.sq_add_sq` already gives `a * a + b * b = -1` mod `p` unconditionally. -/
theorem neg_one_eq_sum_squares_of_ne_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsSumSq (-1 : ℤ_[p]) := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1 : ZMod p)
  have hab' : a * a + b * b = -1 := by simpa [pow_two] using hab
  obtain ⟨z, w, hzw⟩ := hensel_sq_add_const hp2 hab'
  rw [← hzw]
  simpa using IsSumSq.sq_add z (IsSumSq.sq_add w IsSumSq.zero)

/-- `-1` is a sum of (four) squares in `ℤ_[p]` for *any* prime `p`, including `p = 2` where the
Hensel argument behind `neg_one_eq_sum_squares_of_ne_two` is unavailable (the derivative of `X ^ 2`
is `2 * X ≡ 0` mod `2`, never a unit). The argument here is different and needs nothing
`p`-specific: the sum-of-four-squares map `(ℤ_[p])^4 → ℤ_[p]` is continuous on a compact space, so
its range is compact, hence closed; by Lagrange's four-square theorem that range contains the
(dense) image of `ℕ`, so it must be all of `ℤ_[p]`, in particular containing `-1`. -/
theorem neg_one_eq_sum_squares {p : ℕ} [Fact p.Prime] : IsSumSq (-1 : ℤ_[p]) := by
  set f : (ℤ_[p] × ℤ_[p] × ℤ_[p] × ℤ_[p]) → ℤ_[p] :=
    fun x => x.1 * x.1 + x.2.1 * x.2.1 + x.2.2.1 * x.2.2.1 + x.2.2.2 * x.2.2.2 with hfdef
  have hcont : Continuous f := by fun_prop
  have hclosed : IsClosed (Set.range f) := (isCompact_range hcont).isClosed
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[p]) ⊆ Set.range f := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
    refine ⟨((a : ℤ_[p]), (b : ℤ_[p]), (c : ℤ_[p]), (d : ℤ_[p])), ?_⟩
    simp only [hfdef]
    have : ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℕ) : ℤ_[p]) = (n : ℤ_[p]) := by rw [habcd]
    push_cast at this
    linear_combination this
  have hdense : Dense (Set.range f) := PadicInt.denseRange_natCast.mono hsub
  have heq : Set.range f = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  obtain ⟨⟨a, b, c, d⟩, habcd⟩ : (-1 : ℤ_[p]) ∈ Set.range f := heq ▸ Set.mem_univ _
  simp only [hfdef] at habcd
  rw [← habcd, add_assoc, add_assoc]
  simpa using IsSumSq.sq_add a (IsSumSq.sq_add b (IsSumSq.sq_add c (IsSumSq.sq_add d IsSumSq.zero)))

theorem not_injective_to_formallyReal_of_neg_one_eq_sum_squares {p : ℕ} [Fact p.Prime]
    {R M : Type*} [CommRing R] [JordanAlgebra R M] [Nontrivial M] [IsFormallyReal R M]
    (hsq : IsSumSq (-1 : ℤ_[p])) (f : ℤ_[p] →+* R) :
    ¬ Function.Injective f := by
  intro _
  have hsqR : IsSumSq (-1 : R) := by simpa using hsq.map f
  exact (IsFormallyReal.not_of_neg_one_eq_sum_squares (R := R) (M := M) hsqR) inferInstance

/-- No ring hom `ℤ_[p] → R` into the scalar ring of a nontrivial formally real Jordan algebra is
injective, for *any* prime `p`: split on whether `p` is odd (use the explicit two-term
`neg_one_eq_sum_squares_of_ne_two`) or `p = 2` (fall back to the four-term `neg_one_eq_sum_squares`,
which works for every prime but is less economical). -/
theorem not_injective_to_formallyReal {p : ℕ} [Fact p.Prime]
    {R M : Type*} [CommRing R] [JordanAlgebra R M] [Nontrivial M] [IsFormallyReal R M]
    (f : ℤ_[p] →+* R) :
    ¬ Function.Injective f := by
  rcases eq_or_ne p 2 with _ | hp2
  · exact not_injective_to_formallyReal_of_neg_one_eq_sum_squares (M := M)
      neg_one_eq_sum_squares f
  · exact not_injective_to_formallyReal_of_neg_one_eq_sum_squares (M := M)
      (neg_one_eq_sum_squares_of_ne_two hp2) f

end PadicInt
