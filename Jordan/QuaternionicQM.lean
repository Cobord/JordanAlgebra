import Jordan.JordanAlgebra
import Jordan.FormallyReal
import Jordan.MooreDeterminant
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Tactic.LinearCombination

/-!
# The Jordan algebra of quaternionic Hermitian matrices over a general base ring

The `n × n` quaternionic Hermitian matrices form a Jordan algebra under the symmetrized product
`A ∘ B = (A * B + B * A) / 2`. As with `ComplexQM`, the only thing this needs from `ℝ` is `2`
being invertible; the quaternions themselves are just `R` adjoined `i, j` (with `k := i * j`)
satisfying `i * i = c₁ + c₂ * i`, `j * j = c₃`, `j * i = c₂ * j - k` (Mathlib's
`QuaternionAlgebra R c₁ c₂ c₃`, notation `ℍ[R, c₁, c₂, c₃]`), for *any* `c₁ c₂ c₃ : R` -- not just
Hamilton's `c₁ = c₃ = -1, c₂ = 0` (notation `ℍ[R]`). We work over any commutative ring `R` with `2`
invertible, using the associative (non-commutative!) `R`-algebra `Matrix n n ℍ[R, c₁, c₂, c₃]`
with the conjugate-transpose involution (quaternion conjugate on entries). Specializing
`R := ℝ`, `c₁ := -1`, `c₂ := 0`, `c₃ := -1` recovers the classical example.

Note `c₂` only deforms the `i`-square, not the `j`-square: `i * i = c₁ + c₂ * i` is exactly the
same "complete the square" generalization as `QuadraticAlgebra R a b`'s `i ^ 2 = a + b * i`
(needed so the construction still works in characteristic 2, where halving the linear term isn't
possible), applied to build the `i`-direction quadratic extension that the quaternions are then
doubled from; the `j`-extension is a plain Cayley-Dickson doubling step with no such obstruction.
This is also why `star`'s correction term `c₂ * star z.imI` below only touches the `i`-component:
it's exactly the asymmetry already present in the multiplication table, not a separate one.

As in `ComplexQM`, we ask `R` to have a trivial star (it plays the role of `ℝ`, the field fixed by
quaternion conjugation, and could be a proper subring such as `ℚ`). Mathlib's
`QuaternionAlgebra.star` is defined purely from `R`'s ring operations and never looks at any
`Star R` instance; `star_eq_conj_components` records that it agrees with the "conjugate every
component via `R`'s own star" formula precisely because that star is trivial.
-/

open scoped Quaternion

namespace QuaternionicQM

variable (R : Type*) [CommRing R] [StarRing R] [TrivialStar R] [Invertible (2 : R)]
variable (n : Type*) [Fintype n] [DecidableEq n]

section
variable (c₁ c₂ c₃ : R)

omit [Invertible (2 : R)] in
theorem star_eq_conj_components (z : ℍ[R, c₁, c₂, c₃]) :
    star z = ⟨star z.re + c₂ * star z.imI, -star z.imI, -star z.imJ, -star z.imK⟩ := by
  apply QuaternionAlgebra.ext <;> simp [star_trivial]

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
theorem star_algebraMap_eq (r : R) :
    star (algebraMap R (Matrix n n ℍ[R, c₁, c₂, c₃]) r) =
      algebraMap R (Matrix n n ℍ[R, c₁, c₂, c₃]) r := by
  ext i j : 1
  rw [Matrix.star_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  by_cases h : i = j
  · subst h
    apply QuaternionAlgebra.ext <;> simp
  · simp [h, Ne.symm h]

/-- The `n × n` quaternionic Hermitian matrices over `R`, as an `R`-Jordan algebra. -/
def hermitianMatrices : Submodule R (Matrix n n ℍ[R, c₁, c₂, c₃]) :=
  HermitianJordan.hermitian (star_algebraMap_eq R n c₁ c₂ c₃)

noncomputable instance : JordanAlgebra R (hermitianMatrices R n c₁ c₂ c₃) :=
  HermitianJordan.ofInvolutiveAlgebra (star_algebraMap_eq R n c₁ c₂ c₃)

end

/-! ### Formal reality

Over an ordered `R`, restricting to `c₂ = 0` (no loss of generality: `2` invertible already lets
us complete the square, as elsewhere in this file) with `c₁ < 0` and `c₃ < 0` (generalizing
`c₁ = c₃ = -1`, genuine Hamilton quaternions) making the norm form positive-definite, the `n x n`
quaternionic Hermitian matrices are formally real. -/

section FormallyReal

variable [LinearOrder R] [IsStrictOrderedRing R] (c₁ c₃ : R)

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The "norm" of a quaternion (with `c₂ = 0`), as the real part of `q * star q`: a pure ring
identity, no positivity needed. -/
private theorem mul_star_re_eq (q : ℍ[R, c₁, 0, c₃]) :
    (q * star q).re =
      q.re * q.re - c₁ * q.imI * q.imI - c₃ * q.imJ * q.imJ + c₁ * c₃ * q.imK * q.imK := by
  show q.re * (star q).re + c₁ * q.imI * (star q).imI + c₃ * q.imJ * (star q).imJ +
      (0 : R) * c₃ * q.imJ * (star q).imK - c₁ * c₃ * q.imK * (star q).imK = _
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] in
private theorem norm_nonneg (hc₁ : c₁ < 0) (hc₃ : c₃ < 0) (q : ℍ[R, c₁, 0, c₃]) :
    0 ≤ (q * star q).re := by
  rw [mul_star_re_eq]
  have h1 : 0 ≤ q.re * q.re := mul_self_nonneg _
  have h2 : 0 ≤ -c₁ * (q.imI * q.imI) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h3 : 0 ≤ -c₃ * (q.imJ * q.imJ) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h4 : 0 ≤ c₁ * c₃ * (q.imK * q.imK) :=
    mul_nonneg (mul_pos_of_neg_of_neg hc₁ hc₃).le (mul_self_nonneg _)
  nlinarith

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] in
private theorem norm_eq_zero_iff (hc₁ : c₁ < 0) (hc₃ : c₃ < 0) (q : ℍ[R, c₁, 0, c₃]) :
    (q * star q).re = 0 ↔ q = 0 := by
  refine ⟨fun hq => ?_, fun hq => by simp [hq]⟩
  rw [mul_star_re_eq] at hq
  have h1 : 0 ≤ q.re * q.re := mul_self_nonneg _
  have h2 : 0 ≤ -c₁ * (q.imI * q.imI) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h3 : 0 ≤ -c₃ * (q.imJ * q.imJ) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h4 : 0 ≤ c₁ * c₃ * (q.imK * q.imK) :=
    mul_nonneg (mul_pos_of_neg_of_neg hc₁ hc₃).le (mul_self_nonneg _)
  have hre : q.re * q.re = 0 := by nlinarith
  have hI : -c₁ * (q.imI * q.imI) = 0 := by nlinarith
  have hJ : -c₃ * (q.imJ * q.imJ) = 0 := by nlinarith
  have hK : c₁ * c₃ * (q.imK * q.imK) = 0 := by nlinarith
  have hre0 : q.re = 0 := mul_self_eq_zero.mp hre
  have hI0 : q.imI = 0 := by
    rcases mul_eq_zero.mp hI with h | h
    · exact absurd h (by linarith)
    · exact mul_self_eq_zero.mp h
  have hJ0 : q.imJ = 0 := by
    rcases mul_eq_zero.mp hJ with h | h
    · exact absurd h (by linarith)
    · exact mul_self_eq_zero.mp h
  have hK0 : q.imK = 0 := by
    rcases mul_eq_zero.mp hK with h | h
    · exact absurd h (by nlinarith)
    · exact mul_self_eq_zero.mp h
  apply QuaternionAlgebra.ext <;> simp [hre0, hI0, hJ0, hK0]

omit [Invertible (2 : R)] [DecidableEq n] [LinearOrder R] [IsStrictOrderedRing R] in
set_option linter.unusedSectionVars false in
/-- The trace of the Jordan square of a Hermitian matrix corresponds to the sum of norms of its
entries (as a scalar -- `Matrix.trace (A * A)` lands in `ℍ[R, c₁, 0, c₃]`, but it equals the image
of the `R`-valued sum of norms under `algebraMap`). The `[StarRing R] [TrivialStar R]` hypotheses
aren't used by the proof, but are kept as an explicit obligation: they're what justify reading
`star A = A` as the genuine "Hermitian" condition in the first place. -/
theorem trace_mul_self_eq_sum_norm (A : Matrix n n ℍ[R, c₁, 0, c₃]) (hA : star A = A) :
    Matrix.trace (A * A) = algebraMap R ℍ[R, c₁, 0, c₃] (∑ p, ∑ q, (A p q * star (A p q)).re) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have h : A q p = star (A p q) := by
    have h' := congrFun (congrFun hA p) q
    simp only [Matrix.star_apply] at h'
    rw [← h', star_star]
  rw [h]
  exact QuaternionAlgebra.mul_star_eq_coe _

set_option linter.unusedSectionVars false in
/-- The `[StarRing R] [TrivialStar R]` hypotheses aren't used directly by this proof, but are kept
as an explicit obligation: they're what justify `hermitianMatrices` meaning genuine "quaternionic
Hermitian matrices" at all (see the file docstring). -/
theorem isFormallyReal (hc₁ : c₁ < 0) (hc₃ : c₃ < 0) :
    IsFormallyReal R (hermitianMatrices R n c₁ 0 c₃) := by
  refine ⟨fun {ι} _ X hX i => ?_⟩
  have hsum1 : ∑ k, (X k).1 * (X k).1 = 0 := by
    have heq : ∑ k, (X k).1 * (X k).1 = (∑ k, X k * X k : hermitianMatrices R n c₁ 0 c₃).1 := by
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl
        fun k _ => (HermitianJordan.mul_self_eq (star_algebraMap_eq R n c₁ 0 c₃) (X k)).symm
    rw [heq]
    exact congrArg Subtype.val hX
  have htraceR : ∑ k, ∑ p, ∑ q, ((X k).1 p q * star ((X k).1 p q)).re = 0 := by
    have htrace : ∑ k, Matrix.trace ((X k).1 * (X k).1) = 0 := by
      rw [← Matrix.trace_sum, hsum1, Matrix.trace_zero]
    have h2 : algebraMap R ℍ[R, c₁, 0, c₃]
        (∑ k, ∑ p, ∑ q, ((X k).1 p q * star ((X k).1 p q)).re) = 0 := by
      rw [map_sum]
      rw [Finset.sum_congr rfl
        fun k (_ : k ∈ Finset.univ) =>
          (trace_mul_self_eq_sum_norm R n c₁ c₃ (X k).1 (X k).2).symm]
      exact htrace
    have h3 := congrArg QuaternionAlgebra.re h2
    set internal := (∑ k, ∑ p, ∑ q, ((X k : Matrix n n ℍ[R,c₁,c₃]) p q * star ((X k : Matrix n n ℍ[R,c₁,c₃]) p q)).re)
    rw [QuaternionAlgebra.algebraMap_eq] at h3
    simpa using h3
  have hnn : ∀ k ∈ (Finset.univ : Finset ι),
      0 ≤ ∑ p, ∑ q, ((X k).1 p q * star ((X k).1 p q)).re := by
    intro k _
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => norm_nonneg R c₁ c₃ hc₁ hc₃ _
  have heach : ∑ p, ∑ q, ((X i).1 p q * star ((X i).1 p q)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htraceR i (Finset.mem_univ i)
  have hpq : ∀ p ∈ (Finset.univ : Finset n),
      ∑ q, ((X i).1 p q * star ((X i).1 p q)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => Finset.sum_nonneg fun q _ => norm_nonneg R c₁ c₃ hc₁ hc₃ _)).mp heach
  apply Subtype.ext
  apply Matrix.ext
  intro p q
  have hq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => norm_nonneg R c₁ c₃ hc₁ hc₃ _)).mp (hpq p (Finset.mem_univ p)) q (Finset.mem_univ q)
  exact (norm_eq_zero_iff R c₁ c₃ hc₁ hc₃ _).mp hq

/-! #### Generic trace and determinant

The ordinary matrix trace lands directly in `R` after reading off `.re` (the trace of a Hermitian
matrix is genuinely real, though that isn't proved here, matching `ComplexQM`'s house style). The
determinant, however, has no `Matrix.det` to fall back on at all -- `ℍ[R, c₁, 0, c₃]` is
non-commutative -- so it's built from `MooreDeterminant.mooreDetSum` instead: a concrete,
`R`-linear (in the scaling-degree sense of `det_smul`) alternating sum over permutations, read off
via `.re` exactly as the trace is. -/

variable [LinearOrder n]

/-- The `n x n` quaternionic Hermitian matrices have a generic trace and determinant of rank
`Fintype.card n`: the real parts of the ordinary matrix trace and of `mooreDetSum`. -/
noncomputable def detTrace (hc₁ : c₁ < 0) (hc₃ : c₃ < 0) :
    @IsFormallyRealDetTrace R (hermitianMatrices R n c₁ 0 c₃) _ _
      (isFormallyReal R n c₁ c₃ hc₁ hc₃) := by
  letI := isFormallyReal R n c₁ c₃ hc₁ hc₃
  exact
    { rank := Fintype.card n
      trace := (QuaternionAlgebra.reₗ c₁ 0 c₃).comp
        ((Matrix.traceLinearMap n R ℍ[R, c₁, 0, c₃]).comp (hermitianMatrices R n c₁ 0 c₃).subtype)
      det := fun x => (mooreDetSum x.1).re
      det_smul := fun r x => by
        show (mooreDetSum (r • x.1)).re = r ^ Fintype.card n • (mooreDetSum x.1).re
        rw [mooreDetSum_smul, QuaternionAlgebra.re_smul]
      trace_one := by
        show (Matrix.trace (1 : Matrix n n ℍ[R, c₁, 0, c₃])).re = (Fintype.card n : R)
        rw [Matrix.trace_one]
        norm_cast
      det_one := by
        show (mooreDetSum (1 : Matrix n n ℍ[R, c₁, 0, c₃])).re = 1
        rw [mooreDetSum_one]
        rfl }

end FormallyReal

/-! ### Towards conjugation acting on the imaginary part

Over `ℝ`, conjugating Hamilton's quaternions by a `q` with `q * star q = 1` (`x ↦ q * x * star q`)
is an algebra automorphism whose restriction to the "pure imaginary" part `{x | x.re = 0}` (the
span of `i, j, k`) is an honest rotation, i.e. lands in `SO(3)` -- the classical fact that such
quaternions double-cover `SO(3)`, underlying hyperkähler-rotation arguments. `SO(3)` is meaningless
over a general commutative ring `R` (it's a real Lie group, defined using the positive-definite
real inner product), but the algebraic skeleton underneath it -- conjugation by such a `q`
preserving the pure imaginary part -- is purely ring/star-algebra theoretic and makes sense for any
`R`. That skeleton is all this section records.

Specifically: conjugation by any `q` with `q * star q = 1` (what Mathlib calls `unitary`, a name
really suited to the `ℝ`/`ℂ` case rather than a general star ring) is automatically a `*`-algebra
automorphism (`Unitary.conjStarAlgAut`, true in any star ring, nothing quaternion-specific about
it), and any `*`-algebra automorphism preserves the skew-adjoint elements `{x | star x = -x}`
(again completely general). For `c₂ = 0`, the skew-adjoint elements of `ℍ[R, c₁, 0, c₃]` are
exactly the pure imaginary ones, so this conjugation does preserve that subspace. We make no claim
about *what* this action is (it's only literally a rotation when `R = ℝ`), nor whether every
automorphism of the imaginary part arises this way. -/

section Rotation

variable {R} (c₁ c₃ : R)

omit [TrivialStar R] [Invertible (2 : R)] in
/-- Any `*`-algebra automorphism (indeed, any additive `star`-commuting map) sends skew-adjoint
elements to skew-adjoint elements. -/
theorem map_mem_skewAdjoint {A : Type*} [Ring A] [StarRing A] {F : Type*} [FunLike F A A]
    [RingHomClass F A A] [StarHomClass F A A] (f : F) {x : A} (hx : x ∈ skewAdjoint A) :
    f x ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff] at hx ⊢
  rw [← map_star, hx, map_neg]

omit [StarRing R] [TrivialStar R] in
/-- When `c₂ = 0`, the skew-adjoint quaternions are exactly the pure imaginary ones. -/
theorem mem_skewAdjoint_iff_re_eq_zero (z : ℍ[R, c₁, 0, c₃]) :
    z ∈ skewAdjoint ℍ[R, c₁, 0, c₃] ↔ z.re = 0 := by
  rw [skewAdjoint.mem_iff]
  constructor
  · intro h
    have hre : z.re = -z.re := by simpa using congrArg QuaternionAlgebra.re h
    have h2 : (2 : R) * z.re = 0 := by linear_combination hre
    calc z.re = (⅟(2 : R) * 2) * z.re := by rw [invOf_mul_self, one_mul]
      _ = ⅟(2 : R) * ((2 : R) * z.re) := by rw [mul_assoc]
      _ = 0 := by rw [h2, mul_zero]
  · intro h
    apply QuaternionAlgebra.ext <;> simp [h]

omit [TrivialStar R] [Invertible (2 : R)] in
/-- The group homomorphism sending `q` (with `q * star q = 1`) to the automorphism of
`ℍ[R, c₁, 0, c₃]` given by conjugating by it, `x ↦ q * x * star q`. -/
def conjAut : unitary ℍ[R, c₁, 0, c₃] →* (ℍ[R, c₁, 0, c₃] ≃⋆ₐ[R] ℍ[R, c₁, 0, c₃]) :=
  Unitary.conjStarAlgAut R ℍ[R, c₁, 0, c₃]

omit [StarRing R] [TrivialStar R] [Invertible (2 : R)] in
/-- Conjugation by a `q` with `q * star q = 1` preserves the pure imaginary part of
`ℍ[R, c₁, 0, c₃]`. -/
theorem conjAut_mem_skewAdjoint (q : unitary ℍ[R, c₁, 0, c₃]) {x : ℍ[R, c₁, 0, c₃]}
    (hx : x ∈ skewAdjoint ℍ[R, c₁, 0, c₃]) :
    conjAut c₁ c₃ q x ∈ skewAdjoint ℍ[R, c₁, 0, c₃] :=
  map_mem_skewAdjoint (conjAut c₁ c₃ q) hx

end Rotation

end QuaternionicQM
