import Jordan.JordanAlgebra
import Jordan.FormallyReal
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Jordan algebra of symmetric matrices over a general base ring

The `n × n` real symmetric matrices form a real Jordan algebra under the symmetrized product
`A ∘ B = (A * B + B * A) / 2`, obtained from `HermitianJordan` applied to the associative
`ℝ`-algebra `Matrix n n ℝ` with the (trivial, since `ℝ` has trivial star) transpose involution.
As with `ComplexQM`/`QuaternionicQM`, the only thing this needs from `ℝ` is `2` being invertible
and the star structure being trivial; we work over any commutative ring `R` with a trivial star
and `2` invertible. Specializing `R := ℝ` recovers the classical example.
-/

namespace RealQM

variable (R : Type*) [CommRing R] [StarRing R] [TrivialStar R] [Invertible (2 : R)]
variable (n : Type*) [Fintype n] [DecidableEq n]

omit [Invertible (2 : R)] in
theorem star_algebraMap_eq (r : R) :
    star (algebraMap R (Matrix n n R) r) = algebraMap R (Matrix n n R) r := by
  ext i j : 1
  rw [Matrix.star_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The `n × n` symmetric matrices over `R`, as an `R`-Jordan algebra. -/
def symmetricMatrices : Submodule R (Matrix n n R) :=
  HermitianJordan.hermitian (star_algebraMap_eq R n)

noncomputable instance : JordanAlgebra R (symmetricMatrices R n) :=
  HermitianJordan.ofInvolutiveAlgebra (star_algebraMap_eq R n)

/-! ### The `1 x 1` case

A `1 x 1` matrix is trivially symmetric (there's only one entry, so transposing changes nothing),
and the symmetrized product `(AB + BA) / 2` agrees with ordinary multiplication once there's only
one entry to multiply: `symmetricMatrices R (Fin 1)` is literally a copy of `R` itself, with its
own (trivial, `JordanAlgebra.ofCommRing`) Jordan structure. -/

section One

omit [Invertible (2 : R)] in
theorem isSymm_one (A : Matrix (Fin 1) (Fin 1) R) : star A = A := by
  ext i j
  rw [Matrix.star_apply, star_trivial, Subsingleton.elim j i]

/-- Read off the unique entry of a `1 x 1` symmetric matrix. -/
def toR (x : symmetricMatrices R (Fin 1)) : R := x.1 default default

theorem toR_mul (x y : symmetricMatrices R (Fin 1)) : toR R (x * y) = toR R x * toR R y := by
  show ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1)) default default = x.1 default default * y.1 default default
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one,
    Fin.sum_univ_one, smul_eq_mul, Subsingleton.elim (0 : Fin 1) default]
  rw [mul_comm (y.1 default default) (x.1 default default), ← two_mul, ← mul_assoc,
    invOf_mul_self, one_mul]

omit [Invertible (2 : R)] in
theorem toR_add (x y : symmetricMatrices R (Fin 1)) : toR R (x + y) = toR R x + toR R y := rfl

theorem toR_one : toR R (1 : symmetricMatrices R (Fin 1)) = 1 := rfl

omit [Invertible (2 : R)] in
theorem toR_bijective : Function.Bijective (toR R) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    exact hxy
  · intro r
    exact ⟨⟨Matrix.uniqueEquiv.symm r, isSymm_one R _⟩, rfl⟩

/-- Reading off the unique entry of a `1 x 1` symmetric matrix, as a ring hom. -/
def toRHom : symmetricMatrices R (Fin 1) →+* R where
  toFun := toR R
  map_one' := toR_one R
  map_mul' := toR_mul R
  map_zero' := rfl
  map_add' := toR_add R

/-- For `n = 1`, every matrix is trivially symmetric, and the symmetrized Hermitian product
agrees with ordinary multiplication: the symmetric-matrices Jordan algebra is literally a copy of
`R` (with its own multiplication, `JordanAlgebra.ofCommRing`). -/
noncomputable def oneRingEquiv : symmetricMatrices R (Fin 1) ≃+* R :=
  RingEquiv.ofBijective (toRHom R) (toR_bijective R)

end One

/-! ### Formal reality

Over an ordered `R`, the `n x n` symmetric matrices are formally real: `tr(A * A)` is a sum of
squares of the entries of `A` (using that `A` is symmetric to pair each entry with itself, rather
than with its transpose-partner), so a sum of squares vanishing forces every entry of every
summand to vanish. -/

section FormallyReal

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [Invertible (2 : R)] [DecidableEq n] [LinearOrder R] [IsStrictOrderedRing R] in
theorem trace_mul_self_eq_sum_sq (A : Matrix n n R) (hA : star A = A) :
    Matrix.trace (A * A) = ∑ p, ∑ q, A p q * A p q := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have h : A q p = A p q := by
    have h' := congrFun (congrFun hA p) q
    simpa [Matrix.star_apply, star_trivial] using h'
  rw [h]

theorem isFormallyReal : IsFormallyReal R (symmetricMatrices R n) := by
  refine ⟨fun {ι} _ X hX i => ?_⟩
  have hsum1 : ∑ k, (X k).1 * (X k).1 = 0 := by
    have heq : ∑ k, (X k).1 * (X k).1 = (∑ k, X k * X k : symmetricMatrices R n).1 := by
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl
        fun k _ => (HermitianJordan.mul_self_eq (star_algebraMap_eq R n) (X k)).symm
    rw [heq]
    exact congrArg Subtype.val hX
  have htrace : ∑ k, Matrix.trace ((X k).1 * (X k).1) = 0 := by
    rw [← Matrix.trace_sum, hsum1, Matrix.trace_zero]
  have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ Matrix.trace ((X k).1 * (X k).1) := by
    intro k _
    rw [trace_mul_self_eq_sum_sq R n (X k).1 (X k).2]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => mul_self_nonneg _
  have heach : Matrix.trace ((X i).1 * (X i).1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htrace i (Finset.mem_univ i)
  rw [trace_mul_self_eq_sum_sq R n (X i).1 (X i).2] at heach
  have hpq : ∀ p ∈ (Finset.univ : Finset n), ∑ q, (X i).1 p q * (X i).1 p q = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => Finset.sum_nonneg fun q _ => mul_self_nonneg _)).mp heach
  apply Subtype.ext
  ext p q
  have hq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => mul_self_nonneg ((X i).1 p q))).mp (hpq p (Finset.mem_univ p)) q (Finset.mem_univ q)
  exact mul_self_eq_zero.mp hq

/-! #### Generic trace and determinant

The ordinary matrix trace and determinant already land in `R`, so no self-adjointness argument is
needed to extract a generic trace/determinant pair (unlike `ComplexQM`/`QuaternionicQM`, where the
entries live in a larger ring). -/

/-- The `n x n` symmetric matrices have a generic trace and determinant of rank `Fintype.card n`:
the ordinary matrix trace and determinant. -/
noncomputable def detTrace :
    @IsFormallyRealDetTrace R (symmetricMatrices R n) _ _ (isFormallyReal R n) := by
  letI := isFormallyReal R n
  exact
    { rank := Fintype.card n
      trace := (Matrix.traceLinearMap n R R).comp (symmetricMatrices R n).subtype
      det := fun x => Matrix.det x.1
      det_smul := fun r x => by
        show Matrix.det (r • x.1) = r ^ Fintype.card n • Matrix.det x.1
        rw [Matrix.det_smul, smul_eq_mul]
      trace_one := by
        show Matrix.trace (1 : Matrix n n R) = (Fintype.card n : R)
        exact Matrix.trace_one
      det_one := by
        show Matrix.det (1 : Matrix n n R) = 1
        exact Matrix.det_one }

end FormallyReal

end RealQM
