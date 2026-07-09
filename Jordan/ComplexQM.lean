import Jordan.JordanAlgebra
import Jordan.FormallyReal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Jordan algebra of "complex" Hermitian matrices over a general base ring

The motivating example from quantum mechanics is the `n × n` complex Hermitian matrices, forming
a *real* Jordan algebra under the symmetrized product `A ∘ B = (A * B + B * A) / 2`. The only
thing this construction actually needs from `ℝ` is that `2` be invertible; the complex numbers
themselves are just `R` adjoined a root of `X ^ 2 - b * X - a`. So we work over any commutative
ring `R` with `2` invertible, using `ℂ[R, a, b]` (Mathlib's `QuadraticAlgebra R a b`) in place of
`ℂ`, with its built-in conjugate as the involution, for *any* `a b : R` -- not just the `a = -1,
b = 0` (`i ^ 2 = -1`) choice that literally matches `ℂ`. Specializing `R := ℝ`, `a := -1`, `b := 0`
recovers the classical example.

We also ask `R` to have a trivial star: `R` is meant to play the role of `ℝ` (the field fixed by
complex conjugation), so it should itself be star-trivial -- it could equally well be a proper
subring such as `ℚ`, not just `ℝ`.

`Mathlib`'s `QuadraticAlgebra.star` is defined purely from `R`'s *ring* operations --
`star ⟨re, im⟩ = ⟨re + b * im, -im⟩` -- and never looks at any `Star R` instance, even when one is
present. The conjugation one actually wants on a tower built over a star ring -- conjugating each
component too, `⟨star re + b * star im, -star im⟩` -- only agrees with Mathlib's formula because
we assume `TrivialStar R`, i.e. `star = id` on `R`. `star_eq_conj_components` records this
explicitly, so nothing about `R`'s star is silently being discarded here.
-/

/-- Shorthand for `QuadraticAlgebra R a b`, "the complex numbers over `R`" determined by
`i ^ 2 = a + b * i`. -/
scoped[ComplexQM] notation "ℂ[" R "," a "," b "]" => QuadraticAlgebra R a b

namespace ComplexQM

variable (R : Type*) [CommRing R] [StarRing R] [TrivialStar R] [Invertible (2 : R)] (a b : R)
variable (n : Type*) [Fintype n] [DecidableEq n]

omit [Invertible (2 : R)] in
/-- Mathlib's quadratic-algebra conjugate agrees with the "conjugate each component via `R`'s own
star" formula, precisely because `R` has trivial star. -/
theorem star_eq_conj_components (z : ℂ[R, a, b]) :
    star z = ⟨star z.re + b * star z.im, -star z.im⟩ := by
  ext <;> simp [star_trivial]

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] in
theorem star_algebraMap_eq (r : R) :
    star (algebraMap R (Matrix n n (ℂ[R, a, b])) r) =
      algebraMap R (Matrix n n (ℂ[R, a, b])) r := by
  ext i j : 1
  rw [Matrix.star_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  by_cases h : i = j
  · subst h; simp [QuadraticAlgebra.algebraMap_eq]
  · simp [h, Ne.symm h]

/-- The `n × n` "complex" Hermitian matrices over `R`, as an `R`-Jordan algebra. -/
def hermitianMatrices : Submodule R (Matrix n n (ℂ[R, a, b])) :=
  HermitianJordan.hermitian (star_algebraMap_eq R a b n)

noncomputable instance : JordanAlgebra R (hermitianMatrices R a b n) :=
  HermitianJordan.ofInvolutiveAlgebra (star_algebraMap_eq R a b n)

/-! ### Formal reality

Over an ordered `R`, with the discriminant condition `4 * a + b * b < 0` (generalizing `a = -1,
b = 0`, the genuine complex numbers) making the norm form `z.norm` positive-definite, the `n x n`
"complex" Hermitian matrices are formally real: `tr(A * A)` is a sum of norms of the entries of
`A`, each individually nonnegative and zero only at `0`. -/

section FormallyReal

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] [LinearOrder R] [IsStrictOrderedRing R] in
/-- Clearing denominators in "completing the square" for the norm form, so the identity is a pure
ring fact needing no division. -/
private theorem four_mul_norm_eq (z : ℂ[R, a, b]) :
    4 * z.norm =
      (2 * z.re + b * z.im) * (2 * z.re + b * z.im) - (4 * a + b * b) * (z.im * z.im) := by
  rw [QuadraticAlgebra.norm_def]; ring

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] in
private theorem norm_nonneg (hab : 4 * a + b * b < 0) (z : ℂ[R, a, b]) : 0 ≤ z.norm := by
  have h1 : 0 ≤ (2 * z.re + b * z.im) * (2 * z.re + b * z.im) := mul_self_nonneg _
  have h2 : 0 ≤ -(4 * a + b * b) * (z.im * z.im) := mul_nonneg (by linarith) (mul_self_nonneg _)
  nlinarith [four_mul_norm_eq R a b z]

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] in
private theorem norm_eq_zero_iff (hab : 4 * a + b * b < 0) (z : ℂ[R, a, b]) : z.norm = 0 ↔ z = 0 := by
  refine ⟨fun hz => ?_, fun hz => by simp [hz]⟩
  have h1 : 0 ≤ (2 * z.re + b * z.im) * (2 * z.re + b * z.im) := mul_self_nonneg _
  have h2 : 0 ≤ -(4 * a + b * b) * (z.im * z.im) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h4z : (4 : R) * z.norm = 0 := by rw [hz, mul_zero]
  rw [four_mul_norm_eq] at h4z
  have heq1 : (2 * z.re + b * z.im) * (2 * z.re + b * z.im) = 0 := by nlinarith
  have heq2 : -(4 * a + b * b) * (z.im * z.im) = 0 := by nlinarith
  have him0 : z.im = 0 := by
    rcases mul_eq_zero.mp heq2 with h | h
    · exact absurd h (by linarith)
    · exact mul_self_eq_zero.mp h
  have hre2 : (2 * z.re) * (2 * z.re) = 0 := by
    rw [him0, mul_zero, add_zero] at heq1; exact heq1
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hre2 with h | h <;>
      · rw [mul_eq_zero] at h
        rcases h with h | h
        · norm_num at h
        · exact h
  ext <;> simp [hre0, him0]

omit [Invertible (2 : R)] [DecidableEq n] [LinearOrder R] [IsStrictOrderedRing R] in
set_option linter.unusedSectionVars false in
/-- The trace of the Jordan square of a Hermitian matrix corresponds to the sum of norms of its
entries (as a scalar -- `Matrix.trace (A * A)` lands in `ℂ[R, a, b]`, but it equals the image of
the `R`-valued sum of norms under `algebraMap`). The `[StarRing R] [TrivialStar R]` hypotheses
aren't used by the proof, but are kept as an explicit obligation: they're what justify reading
`star A = A` as the genuine "Hermitian" condition in the first place, not just some unrelated
algebraic involution. -/
theorem trace_mul_self_eq_sum_norm (A : Matrix n n (ℂ[R, a, b])) (hA : star A = A) :
    Matrix.trace (A * A) = algebraMap R (ℂ[R, a, b]) (∑ p, ∑ q, (A p q).norm) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have h : A q p = star (A p q) := by
    have h' := congrFun (congrFun hA p) q
    simp only [Matrix.star_apply] at h'
    rw [← h', star_star]
  rw [h, QuadraticAlgebra.algebraMap_norm_eq_mul_star]

set_option linter.unusedSectionVars false in
/-- The `[StarRing R] [TrivialStar R]` hypotheses aren't used directly by this proof, but are kept
as an explicit obligation: they're what justify `hermitianMatrices` meaning genuine "complex
Hermitian matrices" at all (see the file docstring). -/
theorem isFormallyReal (hab : 4 * a + b * b < 0) :
    IsFormallyReal R (hermitianMatrices R a b n) := by
  refine ⟨fun {ι} _ X hX i => ?_⟩
  have hsum1 : ∑ k, (X k).1 * (X k).1 = 0 := by
    have heq : ∑ k, (X k).1 * (X k).1 = (∑ k, X k * X k : hermitianMatrices R a b n).1 := by
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl
        fun k _ => (HermitianJordan.mul_self_eq (star_algebraMap_eq R a b n) (X k)).symm
    rw [heq]
    exact congrArg Subtype.val hX
  have htraceR : ∑ k, ∑ p, ∑ q, ((X k).1 p q).norm = 0 := by
    have htrace : ∑ k, Matrix.trace ((X k).1 * (X k).1) = 0 := by
      rw [← Matrix.trace_sum, hsum1, Matrix.trace_zero]
    have h2 : algebraMap R (ℂ[R, a, b]) (∑ k, ∑ p, ∑ q, ((X k).1 p q).norm) = 0 := by
      rw [map_sum]
      rw [Finset.sum_congr rfl
        fun k (_ : k ∈ Finset.univ) => (trace_mul_self_eq_sum_norm R a b n (X k).1 (X k).2).symm]
      exact htrace
    have h3 := congrArg QuadraticAlgebra.re h2
    rwa [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_zero] at h3
  have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ ∑ p, ∑ q, ((X k).1 p q).norm := by
    intro k _
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => norm_nonneg R a b hab _
  have heach : ∑ p, ∑ q, ((X i).1 p q).norm = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htraceR i (Finset.mem_univ i)
  have hpq : ∀ p ∈ (Finset.univ : Finset n), ∑ q, ((X i).1 p q).norm = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => Finset.sum_nonneg fun q _ => norm_nonneg R a b hab _)).mp heach
  apply Subtype.ext
  apply Matrix.ext
  intro p q
  have hq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => norm_nonneg R a b hab _)).mp (hpq p (Finset.mem_univ p)) q (Finset.mem_univ q)
  exact (norm_eq_zero_iff R a b hab _).mp hq

/-! #### Generic trace and determinant

For Hermitian `A`, both `Matrix.trace A` and `Matrix.det A` are self-adjoint elements of
`ℂ[R, a, b]` (`star` commutes with `trace`/`det` via `Aᴴ = A`), hence lie in the image of
`algebraMap R _`; reading off their real part (`.re`) therefore recovers the genuine `R`-valued
trace/determinant, not merely a projection that discards information. -/

omit [StarRing R] [TrivialStar R] [LinearOrder R] [IsStrictOrderedRing R] in
private theorem eq_algebraMap_re_of_star_eq (z : ℂ[R, a, b]) (hz : star z = z) :
    z = algebraMap R (ℂ[R, a, b]) z.re := by
  have him : z.im = -z.im := by
    have h := congrArg QuadraticAlgebra.im hz
    simpa using h.symm
  have h2 : (2 : R) • z.im = 0 := by
    rw [two_smul, add_eq_zero_iff_eq_neg]; exact him
  have him0 : z.im = 0 := by
    have h3 := congrArg (⅟(2 : R) • ·) h2
    simpa [smul_smul] using h3
  ext
  · simp [QuadraticAlgebra.algebraMap_eq]
  · simp [QuadraticAlgebra.algebraMap_eq, him0]

omit [StarRing R] [TrivialStar R] [DecidableEq n] [LinearOrder R] [IsStrictOrderedRing R] in
theorem trace_eq_algebraMap (A : Matrix n n ℂ[R, a, b]) (hA : star A = A) :
    Matrix.trace A = algebraMap R (ℂ[R, a, b]) (Matrix.trace A).re := by
  apply eq_algebraMap_re_of_star_eq
  have h := Matrix.trace_conjTranspose A
  rw [← Matrix.star_eq_conjTranspose, hA] at h
  exact h.symm

omit [StarRing R] [TrivialStar R] [LinearOrder R] [IsStrictOrderedRing R] in
theorem det_eq_algebraMap (A : Matrix n n ℂ[R, a, b]) (hA : star A = A) :
    Matrix.det A = algebraMap R (ℂ[R, a, b]) (Matrix.det A).re := by
  apply eq_algebraMap_re_of_star_eq
  have h := Matrix.det_conjTranspose A
  rw [← Matrix.star_eq_conjTranspose, hA] at h
  exact h.symm

/-- The `n x n` "complex" Hermitian matrices have a generic trace and determinant of rank
`Fintype.card n`: the real parts of the ordinary matrix trace and determinant, which
`trace_eq_algebraMap`/`det_eq_algebraMap` show genuinely recover them. -/
noncomputable def detTrace (hab : 4 * a + b * b < 0) :
    @IsFormallyRealDetTrace R (hermitianMatrices R a b n) _ _ (isFormallyReal R a b n hab) := by
  letI := isFormallyReal R a b n hab
  exact
    { rank := Fintype.card n
      trace := (QuadraticAlgebra.reₗ a b).comp
        ((Matrix.traceLinearMap n R (ℂ[R, a, b])).comp (hermitianMatrices R a b n).subtype)
      det := fun x => (Matrix.det x.1).re
      det_smul := fun r x => by
        show (Matrix.det (r • x.1)).re = r ^ Fintype.card n • (Matrix.det x.1).re
        rw [Matrix.det_smul_of_tower, QuadraticAlgebra.re_smul]
      trace_one := by
        show (Matrix.trace (1 : Matrix n n (ℂ[R, a, b]))).re = (Fintype.card n : R)
        rw [Matrix.trace_one]
        norm_cast
      det_one := by
        show (Matrix.det (1 : Matrix n n (ℂ[R, a, b]))).re = 1
        rw [Matrix.det_one, QuadraticAlgebra.re_one] }

end FormallyReal

end ComplexQM
