import Jordan.HermitianMatrixAssociator
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Jordan identity for `H_3(D,-)`

McCrimmon's `3x3` Coordinate Theorem C.1.3 (*A Taste of Jordan Algebras*, Appendix C.1): the Jordan
identity `[A,B,A^2]+ = 0` (in `plus_associator_eq`'s undivided brace-product form) for Hermitian
`3 x 3` matrices `A B` over a coordinate ring `D` with a nuclear involution, `D` alternative. This
file proves each of the six matrix positions (`hermitian_jordan_diag0/1/2`,
`hermitian_jordan_offdiag01/02/12`) and assembles them into the full statement
(`hermitian_jordan_identity`): the *whole* matrix `[A,B,A^2]+` vanishes, not just one entry. The
three positions not proved directly (`(1,0)`, `(2,0)`, `(2,1)`) follow for free from the other three
plus the fact that `[A,B,A^2]+` is itself always Hermitian (given `A`, `B` Hermitian) -- so their
`star`-conjugate (upper-triangular) partners already vanishing forces them to vanish too, via
`star 0 = 0`.

This file needs `[StarRing D]` (`star` an anti-automorphism of multiplication, `star (x*y) = star y
* star x`) in addition to `[IsNuclearInvolution D]`'s own `[StarAddMonoid D]` -- kept in a separate
file from `HermitianMatrixAssociator.lean` specifically so the two are never *both* declared as
section variables at once: `StarRing D` already implies `StarAddMonoid D` via a registered Mathlib
instance, and declaring both independently creates a `Star D` instance diamond (Lean warns about
this directly: "`[StarAddMonoid D]` and `[StarRing D]` can be used to infer conflicting versions of
`[Star D]`"), which silently breaks `rw`/`simp` matching on `star`-headed terms.
-/

open IsAlternative
open scoped Matrix

/-- `star` is anti-multiplicative on the associator -- needs no alternativity at all, just that
`star` is an additive, multiplicative anti-automorphism (`StarRing`). The associator-level analogue
of `star (x*y) = star y * star x`. -/
theorem star_associator {M : Type*} [NonUnitalNonAssocRing M] [StarRing M] (x y z : M) :
    star (associator x y z) = -associator (star z) (star y) (star x) := by
  unfold associator
  rw [star_sub]
  simp only [star_mul]
  abel

/-- The matrix-level analogue of `star_associator`, via `Matrix.conjTranspose_mul` directly rather
than a bundled `StarRing (Matrix ...)` instance (avoiding the need to register one). -/
theorem matrix_associator_conjTranspose {D : Type*} [NonUnitalNonAssocRing D] [StarRing D]
    (M N P : Matrix (Fin 3) (Fin 3) D) :
    (associator M N P)ᴴ = -associator (Pᴴ) (Nᴴ) (Mᴴ) := by
  unfold associator
  rw [Matrix.conjTranspose_sub]
  simp only [Matrix.conjTranspose_mul]
  abel

variable {D : Type*} [NonUnitalNonAssocRing D] [IsAlternative D] [StarRing D]
  [IsNuclearInvolution D]

omit [IsAlternative D] [IsNuclearInvolution D] in
/-- The square of a Hermitian matrix is Hermitian. -/
theorem hermitian_sq {A : Matrix (Fin 3) (Fin 3) D} (hA : A.IsHermitian) :
    (A * A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, hA.eq]

/-- The `(1,0)` mirror of `matrix_associator_offdiag01_self`, via `matrix_associator_conjTranspose`
applied to the self-associator `associator A A A` (Hermitian, since `Aᴴ = A`): its conjugate
transpose is `-associator A A A` itself, so the `(1,0)` entry is (minus the `star` of) the already-
known-zero `(0,1)` entry. -/
theorem matrix_associator_offdiag10_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 1 0 = 0 := by
  have h := matrix_associator_conjTranspose A A A
  rw [hA.eq] at h
  have h10 : (associator A A A)ᴴ 1 0 = -associator A A A 1 0 := by rw [h]; rfl
  rw [Matrix.conjTranspose_apply, matrix_associator_offdiag01_self A hA] at h10
  simpa using h10.symm

/-- The `(2,0)` mirror of `matrix_associator_offdiag02_self`, exactly like
`matrix_associator_offdiag10_self`. -/
theorem matrix_associator_offdiag20_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 2 0 = 0 := by
  have h := matrix_associator_conjTranspose A A A
  rw [hA.eq] at h
  have h20 : (associator A A A)ᴴ 2 0 = -associator A A A 2 0 := by rw [h]; rfl
  rw [Matrix.conjTranspose_apply, matrix_associator_offdiag02_self A hA] at h20
  simpa using h20.symm

/-- The `(2,1)` mirror of `matrix_associator_offdiag12_self`, exactly like
`matrix_associator_offdiag10_self`. Needed for *both* the `(1,1)` and `(2,2)` diagonal Jordan-
identity entries (it's the one off-diagonal position not already covered by
`offdiag10/20_self`). -/
theorem matrix_associator_offdiag21_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 2 1 = 0 := by
  have h := matrix_associator_conjTranspose A A A
  rw [hA.eq] at h
  have h21 : (associator A A A)ᴴ 2 1 = -associator A A A 2 1 := by rw [h]; rfl
  rw [Matrix.conjTranspose_apply, matrix_associator_offdiag12_self A hA] at h21
  simpa using h21.symm

/-- **The `(0,0)` diagonal entry of McCrimmon's `3x3` Coordinate Theorem C.1.3**: the Jordan
identity `[A,B,A^2]+ = 0` for Hermitian `A B` over an alternative coordinate ring `D` with nuclear
involution, at matrix position `(0,0)`. Assembled from `plus_associator_eq` (McCrimmon's (1.1.1),
reducing the brace-associator to ordinary associators and a commutator), `matrix_associator_diag0`
(McCrimmon's (1.2.1): three of the four resulting associator-pairs vanish at `(0,0)` by their own
built-in `X ↔ Z` symmetry -- no need for `mccrimmon_key_identity` at this diagonal position, unlike
the harder off-diagonal case), `matrix_associator_diag0_self`/`offdiag01/02/10/20_self` (McCrimmon's
(1.2.2)/(1.2.4), showing the matrix commutator `A*(A*A) - (A*A)*A` is diagonal with `(0,0)` entry
`-2 * associator (A 0 1) (A 1 2) (A 2 0)`), and finally `nuclear_comm_associator` (Nuclear Slipping)
to show the diagonal Hermitian entry `B 0 0` commutes with that associator value. -/
theorem hermitian_jordan_diag0 (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)) 0 0 = 0 := by
  have hC : (A * A).IsHermitian := hermitian_sq hA
  have h00 := congrFun (congrFun (plus_associator_eq A B (A * A)) 0) 0
  rw [h00]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have hB00 : IsNuclear (B 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 0 0)
  have sym1 : associator A B (A * A) 0 0 = associator (A * A) B A 0 0 := by
    rw [matrix_associator_diag0 A B (A * A) hA hB hC, matrix_associator_diag0 (A * A) B A hC hB hA]
    abel
  have sym2 : associator B A (A * A) 0 0 = associator (A * A) A B 0 0 := by
    rw [matrix_associator_diag0 B A (A * A) hB hA hC, matrix_associator_diag0 (A * A) A B hC hA hB]
    abel
  have sym3 : associator A (A * A) B 0 0 = associator B (A * A) A 0 0 := by
    rw [matrix_associator_diag0 A (A * A) B hA hC hB, matrix_associator_diag0 B (A * A) A hB hC hA]
    abel
  have hN : A * (A * A) - A * A * A = -associator A A A := by unfold associator; abel
  have hcomm : (B * (A * (A * A) - A * A * A)) 0 0 - ((A * (A * A) - A * A * A) * B) 0 0 = 0 := by
    rw [hN]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.neg_apply]
    rw [matrix_associator_offdiag01_self A hA, matrix_associator_offdiag20_self A hA,
      matrix_associator_offdiag02_self A hA, matrix_associator_offdiag10_self A hA,
      matrix_associator_diag0_self A hA, two_smul]
    have key := nuclear_comm_associator hB00 (A 0 1) (A 1 2) (A 2 0)
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_add, add_mul, mul_neg, neg_mul]
    linear_combination (norm := abel) -key - key
  linear_combination (norm := abel) sym1 + sym2 + sym3 + hcomm

/-- The `(1,1)` analogue of `hermitian_jordan_diag0`, via `matrix_associator_diag1` and the
`(1,1)`-adjacent off-diagonal facts. -/
theorem hermitian_jordan_diag1 (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)) 1 1 = 0 := by
  have hC : (A * A).IsHermitian := hermitian_sq hA
  have h11 := congrFun (congrFun (plus_associator_eq A B (A * A)) 1) 1
  rw [h11]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have hB11 : IsNuclear (B 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 1 1)
  have sym1 : associator A B (A * A) 1 1 = associator (A * A) B A 1 1 := by
    rw [matrix_associator_diag1 A B (A * A) hA hB hC, matrix_associator_diag1 (A * A) B A hC hB hA]
    abel
  have sym2 : associator B A (A * A) 1 1 = associator (A * A) A B 1 1 := by
    rw [matrix_associator_diag1 B A (A * A) hB hA hC, matrix_associator_diag1 (A * A) A B hC hA hB]
    abel
  have sym3 : associator A (A * A) B 1 1 = associator B (A * A) A 1 1 := by
    rw [matrix_associator_diag1 A (A * A) B hA hC hB, matrix_associator_diag1 B (A * A) A hB hC hA]
    abel
  have hN : A * (A * A) - A * A * A = -associator A A A := by unfold associator; abel
  have hcomm : (B * (A * (A * A) - A * A * A)) 1 1 - ((A * (A * A) - A * A * A) * B) 1 1 = 0 := by
    rw [hN]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.neg_apply]
    rw [matrix_associator_offdiag01_self A hA, matrix_associator_offdiag21_self A hA,
      matrix_associator_offdiag12_self A hA, matrix_associator_offdiag10_self A hA,
      matrix_associator_diag1_self A hA, two_smul]
    have key := nuclear_comm_associator hB11 (A 1 2) (A 2 0) (A 0 1)
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_add, add_mul, mul_neg, neg_mul]
    linear_combination (norm := abel) -key - key
  linear_combination (norm := abel) sym1 + sym2 + sym3 + hcomm

/-- The `(2,2)` analogue of `hermitian_jordan_diag0`, via `matrix_associator_diag2` and the
`(2,2)`-adjacent off-diagonal facts. -/
theorem hermitian_jordan_diag2 (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)) 2 2 = 0 := by
  have hC : (A * A).IsHermitian := hermitian_sq hA
  have h22 := congrFun (congrFun (plus_associator_eq A B (A * A)) 2) 2
  rw [h22]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have hB22 : IsNuclear (B 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 2 2)
  have sym1 : associator A B (A * A) 2 2 = associator (A * A) B A 2 2 := by
    rw [matrix_associator_diag2 A B (A * A) hA hB hC, matrix_associator_diag2 (A * A) B A hC hB hA]
    abel
  have sym2 : associator B A (A * A) 2 2 = associator (A * A) A B 2 2 := by
    rw [matrix_associator_diag2 B A (A * A) hB hA hC, matrix_associator_diag2 (A * A) A B hC hA hB]
    abel
  have sym3 : associator A (A * A) B 2 2 = associator B (A * A) A 2 2 := by
    rw [matrix_associator_diag2 A (A * A) B hA hC hB, matrix_associator_diag2 B (A * A) A hB hC hA]
    abel
  have hN : A * (A * A) - A * A * A = -associator A A A := by unfold associator; abel
  have hcomm : (B * (A * (A * A) - A * A * A)) 2 2 - ((A * (A * A) - A * A * A) * B) 2 2 = 0 := by
    rw [hN]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.neg_apply]
    rw [matrix_associator_offdiag02_self A hA, matrix_associator_offdiag21_self A hA,
      matrix_associator_offdiag12_self A hA, matrix_associator_offdiag20_self A hA,
      matrix_associator_diag2_self A hA, two_smul]
    have key := nuclear_comm_associator hB22 (A 2 0) (A 0 1) (A 1 2)
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_add, add_mul, mul_neg, neg_mul]
    linear_combination (norm := abel) -key - key
  linear_combination (norm := abel) sym1 + sym2 + sym3 + hcomm

/-- **The `(0,1)` off-diagonal entry of McCrimmon's `3x3` Coordinate Theorem C.1.3** -- the harder
case his own proof (p. 479) singles out as needing more than the diagonal case. Where the diagonal
positions only needed `matrix_associator_diagN`'s built-in symmetry, here the analogous
"positive"/"negative" three-term sums (`pos`/`neg` below, from `matrix_associator_offdiag01` applied
to the three cyclic-ish orderings of `(A,B,C)` and of `(C,B,A)`) only collapse down to a genuinely
new quantity `t01` (not to zero), matching McCrimmon's `t12`. Closing `t01 + [B01,a] = 0` (the `t01`
`have` block below) needs the *actual matrix-squaring formula* for `(A*A)`'s off-diagonal entries
(via `Matrix.mul_apply`/`Fin.sum_univ_three`), `nuclear_slip_last`/`nuclear_slip_last_right` to kill
the two nuclear-diagonal-touching terms in each entry (leaving one surviving product each), the
Hermitian relations converting those into `star`-headed products (`e1`/`e2`/`e3`, using `star_mul`'s
anti-automorphism law to recognize e.g. `A 0 2 * A 2 1 = star (A 1 2 * A 2 0)`), `assoc_star_last` to
strip the resulting `star`, and finally `mccrimmon_key_identity` (McCrimmon's (1.1.2)) itself to
close the loop -- exactly the identity McCrimmon cites at this exact step ("vanishes by Alternative
Associator Fact (1.1.2)"). -/
theorem hermitian_jordan_offdiag01 (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)) 0 1 = 0 := by
  have hC : (A * A).IsHermitian := hermitian_sq hA
  have h01 := congrFun (congrFun (plus_associator_eq A B (A * A)) 0) 1
  rw [h01]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have pos : associator A B (A * A) 0 1 + associator B A (A * A) 0 1
      + associator A (A * A) B 0 1 =
      -(associator (B 0 1) (A 0 1) ((A * A) 0 1) + associator (B 0 1) (A 1 2) ((A * A) 1 2)
        + associator (B 0 1) (A 2 0) ((A * A) 2 0)) := by
    rw [matrix_associator_offdiag01 A B (A * A) hA hB hC,
      matrix_associator_offdiag01 B A (A * A) hB hA hC,
      matrix_associator_offdiag01 A (A * A) B hA hC hB]
    have s1 : associator (A 0 1) (B 0 1) ((A * A) 0 1)
        = -associator (B 0 1) (A 0 1) ((A * A) 0 1) :=
      associator_swap_first (A 0 1) (B 0 1) ((A * A) 0 1)
    have s2 : associator (A 0 1) ((A * A) 0 1) (B 0 1)
        = -associator (A 0 1) (B 0 1) ((A * A) 0 1) := by
      linear_combination (norm := abel) associator_swap_last (A 0 1) (B 0 1) ((A * A) 0 1)
    have s3 : associator (A 0 1) ((A * A) 1 2) (B 1 2)
        = -associator (A 0 1) (B 1 2) ((A * A) 1 2) := by
      linear_combination (norm := abel) associator_swap_last (A 0 1) (B 1 2) ((A * A) 1 2)
    have s4 : associator (B 2 0) (A 2 0) ((A * A) 0 1)
        = -associator (A 2 0) (B 2 0) ((A * A) 0 1) :=
      associator_swap_first (B 2 0) (A 2 0) ((A * A) 0 1)
    have s5 : associator (A 2 0) ((A * A) 2 0) (B 0 1)
        = associator (B 0 1) (A 2 0) ((A * A) 2 0) :=
      (associator_cyclic (A 2 0) ((A * A) 2 0) (B 0 1)).trans
        (associator_cyclic ((A * A) 2 0) (B 0 1) (A 2 0))
    simp only [s1, s2, s3, s4, s5]
    abel
  have neg : associator (A * A) B A 0 1 + associator (A * A) A B 0 1
      + associator B (A * A) A 0 1 =
      associator (B 0 1) (A 0 1) ((A * A) 0 1) + associator (B 0 1) (A 1 2) ((A * A) 1 2)
        + associator (B 0 1) (A 2 0) ((A * A) 2 0) := by
    rw [matrix_associator_offdiag01 (A * A) B A hC hB hA,
      matrix_associator_offdiag01 (A * A) A B hC hA hB,
      matrix_associator_offdiag01 B (A * A) A hB hC hA]
    have fa : associator ((A * A) 0 1) (B 0 1) (A 0 1)
        = -associator ((A * A) 0 1) (A 0 1) (B 0 1) :=
      associator_swap_last ((A * A) 0 1) (B 0 1) (A 0 1)
    have fb : associator (B 0 1) ((A * A) 0 1) (A 0 1)
        = -associator ((A * A) 0 1) (B 0 1) (A 0 1) :=
      associator_swap_first (B 0 1) ((A * A) 0 1) (A 0 1)
    have fd : associator ((A * A) 0 1) (B 1 2) (A 1 2)
        = -associator ((A * A) 0 1) (A 1 2) (B 1 2) :=
      associator_swap_last ((A * A) 0 1) (B 1 2) (A 1 2)
    have fe : associator (B 0 1) ((A * A) 1 2) (A 1 2)
        = -associator (B 0 1) (A 1 2) ((A * A) 1 2) :=
      associator_swap_last (B 0 1) ((A * A) 1 2) (A 1 2)
    have ff : associator ((A * A) 2 0) (B 2 0) (A 0 1)
        = -associator (B 2 0) ((A * A) 2 0) (A 0 1) :=
      associator_swap_first ((A * A) 2 0) (B 2 0) (A 0 1)
    have fg : associator ((A * A) 2 0) (A 2 0) (B 0 1)
        = associator (A 2 0) (B 0 1) ((A * A) 2 0) :=
      associator_cyclic ((A * A) 2 0) (A 2 0) (B 0 1)
    have fh : associator (A 2 0) (B 0 1) ((A * A) 2 0)
        = associator (B 0 1) ((A * A) 2 0) (A 2 0) :=
      associator_cyclic (A 2 0) (B 0 1) ((A * A) 2 0)
    have fi : associator (B 0 1) ((A * A) 2 0) (A 2 0)
        = -associator (B 0 1) (A 2 0) ((A * A) 2 0) :=
      associator_swap_last (B 0 1) ((A * A) 2 0) (A 2 0)
    have fj : associator ((A * A) 0 1) (A 0 1) (B 0 1)
        = -associator (B 0 1) (A 0 1) ((A * A) 0 1) := by
      rw [associator_cyclic ((A * A) 0 1) (A 0 1) (B 0 1)]
      exact associator_swap_first (A 0 1) (B 0 1) ((A * A) 0 1)
    simp only [fa, fb, fd, fe, ff, fg, fh, fi, fj]
    abel
  have hN : A * (A * A) - A * A * A = -associator A A A := by unfold associator; abel
  have hcomm : (B * (A * (A * A) - A * A * A)) 0 1 - ((A * (A * A) - A * A * A) * B) 0 1
      = (2 : ℕ) • (associator (A 0 1) (A 1 2) (A 2 0) * B 0 1
        - B 0 1 * associator (A 0 1) (A 1 2) (A 2 0)) := by
    rw [hN]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.neg_apply]
    rw [matrix_associator_offdiag01_self A hA, matrix_associator_offdiag21_self A hA,
      matrix_associator_offdiag02_self A hA,
      matrix_associator_diag1_self A hA, matrix_associator_diag0_self A hA, two_smul]
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_add, mul_neg, neg_mul]
    rw [show associator (A 1 2) (A 2 0) (A 0 1) = associator (A 0 1) (A 1 2) (A 2 0) from
      (associator_cyclic (A 0 1) (A 1 2) (A 2 0)).symm]
    simp only [smul_mul_assoc]
    abel
  have t01 : associator (B 0 1) (A 0 1) ((A * A) 0 1) + associator (B 0 1) (A 1 2) ((A * A) 1 2)
      + associator (B 0 1) (A 2 0) ((A * A) 2 0)
      + (B 0 1 * associator (A 0 1) (A 1 2) (A 2 0) - associator (A 0 1) (A 1 2) (A 2 0) * B 0 1)
      = 0 := by
    have hA00 : IsNuclear (A 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 0 0)
    have hA11 : IsNuclear (A 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 1 1)
    have hA22 : IsNuclear (A 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 2 2)
    have r1 : associator (B 0 1) (A 0 1) ((A * A) 0 1)
        = associator (B 0 1) (A 0 1) (A 0 2 * A 2 1) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      rw [associator_add_right, associator_add_right,
        nuclear_slip_last hA00 (B 0 1) (A 0 1) (A 0 1),
        nuclear_slip_last_right hA11 (B 0 1) (A 0 1) (A 0 1),
        associator_right_self (A 0 1) (B 0 1), mul_zero, zero_mul]
      abel
    have r2 : associator (B 0 1) (A 1 2) ((A * A) 1 2)
        = associator (B 0 1) (A 1 2) (A 1 0 * A 0 2) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      rw [associator_add_right, associator_add_right,
        nuclear_slip_last hA11 (B 0 1) (A 1 2) (A 1 2),
        nuclear_slip_last_right hA22 (B 0 1) (A 1 2) (A 1 2),
        associator_right_self (A 1 2) (B 0 1), mul_zero, zero_mul]
      abel
    have r3 : associator (B 0 1) (A 2 0) ((A * A) 2 0)
        = associator (B 0 1) (A 2 0) (A 2 1 * A 1 0) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      rw [associator_add_right, associator_add_right,
        nuclear_slip_last_right hA00 (B 0 1) (A 2 0) (A 2 0),
        nuclear_slip_last hA22 (B 0 1) (A 2 0) (A 2 0),
        associator_right_self (A 2 0) (B 0 1), mul_zero, zero_mul]
      abel
    rw [r1, r2, r3]
    have e1 : A 0 2 * A 2 1 = star (A 1 2 * A 2 0) := by
      rw [star_mul, ← hA.apply 2 0, ← hA.apply 1 2, star_star, star_star]
    have e2 : A 1 0 * A 0 2 = star (A 2 0 * A 0 1) := by
      rw [star_mul, ← hA.apply 0 1, ← hA.apply 2 0, star_star, star_star]
    have e3 : A 2 1 * A 1 0 = star (A 0 1 * A 1 2) := by
      rw [star_mul, ← hA.apply 1 2, ← hA.apply 0 1, star_star, star_star]
    rw [e1, e2, e3, assoc_star_last, assoc_star_last, assoc_star_last]
    have key := mccrimmon_key_identity (B 0 1) (A 0 1) (A 1 2) (A 2 0)
    linear_combination (norm := abel) key
  linear_combination (norm := abel) pos - neg + hcomm - 2 • t01

/-- The `(1,2)` analogue of `hermitian_jordan_offdiag01`. Unlike the diagonal cases, off-diagonal
positions aren't all related by the same simple cyclic shift: `(0,1) → (1,2) → (2,0)` *is* a shift
orbit (`matrix_associator_offdiag12` is literally the `0→1→2→0` cyclic shift of
`matrix_associator_offdiag01`'s own conclusion), so this proof is exactly `hermitian_jordan_offdiag01`
with every index shifted -- it worked on the first try, no debugging needed. `(0,2)`, the *other*
unordered off-diagonal pair, is a genuinely different case (see `hermitian_jordan_offdiag02` below,
which needs its own derivation). -/
theorem hermitian_jordan_offdiag12 (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)) 1 2 = 0 := by
  have hC : (A * A).IsHermitian := hermitian_sq hA
  have h12 := congrFun (congrFun (plus_associator_eq A B (A * A)) 1) 2
  rw [h12]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have pos : associator A B (A * A) 1 2 + associator B A (A * A) 1 2
      + associator A (A * A) B 1 2 =
      -(associator (B 1 2) (A 1 2) ((A * A) 1 2) + associator (B 1 2) (A 2 0) ((A * A) 2 0)
        + associator (B 1 2) (A 0 1) ((A * A) 0 1)) := by
    rw [matrix_associator_offdiag12 A B (A * A) hA hB hC,
      matrix_associator_offdiag12 B A (A * A) hB hA hC,
      matrix_associator_offdiag12 A (A * A) B hA hC hB]
    have s1 : associator (A 1 2) (B 1 2) ((A * A) 1 2)
        = -associator (B 1 2) (A 1 2) ((A * A) 1 2) :=
      associator_swap_first (A 1 2) (B 1 2) ((A * A) 1 2)
    have s2 : associator (A 1 2) ((A * A) 1 2) (B 1 2)
        = -associator (A 1 2) (B 1 2) ((A * A) 1 2) := by
      linear_combination (norm := abel) associator_swap_last (A 1 2) (B 1 2) ((A * A) 1 2)
    have s3 : associator (A 1 2) ((A * A) 2 0) (B 2 0)
        = -associator (A 1 2) (B 2 0) ((A * A) 2 0) := by
      linear_combination (norm := abel) associator_swap_last (A 1 2) (B 2 0) ((A * A) 2 0)
    have s4 : associator (B 0 1) (A 0 1) ((A * A) 1 2)
        = -associator (A 0 1) (B 0 1) ((A * A) 1 2) :=
      associator_swap_first (B 0 1) (A 0 1) ((A * A) 1 2)
    have s5 : associator (A 0 1) ((A * A) 0 1) (B 1 2)
        = associator (B 1 2) (A 0 1) ((A * A) 0 1) :=
      (associator_cyclic (A 0 1) ((A * A) 0 1) (B 1 2)).trans
        (associator_cyclic ((A * A) 0 1) (B 1 2) (A 0 1))
    simp only [s1, s2, s3, s4, s5]
    abel
  have neg : associator (A * A) B A 1 2 + associator (A * A) A B 1 2
      + associator B (A * A) A 1 2 =
      associator (B 1 2) (A 1 2) ((A * A) 1 2) + associator (B 1 2) (A 2 0) ((A * A) 2 0)
        + associator (B 1 2) (A 0 1) ((A * A) 0 1) := by
    rw [matrix_associator_offdiag12 (A * A) B A hC hB hA,
      matrix_associator_offdiag12 (A * A) A B hC hA hB,
      matrix_associator_offdiag12 B (A * A) A hB hC hA]
    have fa : associator ((A * A) 1 2) (B 1 2) (A 1 2)
        = -associator ((A * A) 1 2) (A 1 2) (B 1 2) :=
      associator_swap_last ((A * A) 1 2) (B 1 2) (A 1 2)
    have fb : associator (B 1 2) ((A * A) 1 2) (A 1 2)
        = -associator ((A * A) 1 2) (B 1 2) (A 1 2) :=
      associator_swap_first (B 1 2) ((A * A) 1 2) (A 1 2)
    have fd : associator ((A * A) 1 2) (B 2 0) (A 2 0)
        = -associator ((A * A) 1 2) (A 2 0) (B 2 0) :=
      associator_swap_last ((A * A) 1 2) (B 2 0) (A 2 0)
    have fe : associator (B 1 2) ((A * A) 2 0) (A 2 0)
        = -associator (B 1 2) (A 2 0) ((A * A) 2 0) :=
      associator_swap_last (B 1 2) ((A * A) 2 0) (A 2 0)
    have ff : associator ((A * A) 0 1) (B 0 1) (A 1 2)
        = -associator (B 0 1) ((A * A) 0 1) (A 1 2) :=
      associator_swap_first ((A * A) 0 1) (B 0 1) (A 1 2)
    have fg : associator ((A * A) 0 1) (A 0 1) (B 1 2)
        = associator (A 0 1) (B 1 2) ((A * A) 0 1) :=
      associator_cyclic ((A * A) 0 1) (A 0 1) (B 1 2)
    have fh : associator (A 0 1) (B 1 2) ((A * A) 0 1)
        = associator (B 1 2) ((A * A) 0 1) (A 0 1) :=
      associator_cyclic (A 0 1) (B 1 2) ((A * A) 0 1)
    have fi : associator (B 1 2) ((A * A) 0 1) (A 0 1)
        = -associator (B 1 2) (A 0 1) ((A * A) 0 1) :=
      associator_swap_last (B 1 2) ((A * A) 0 1) (A 0 1)
    have fj : associator ((A * A) 1 2) (A 1 2) (B 1 2)
        = -associator (B 1 2) (A 1 2) ((A * A) 1 2) := by
      rw [associator_cyclic ((A * A) 1 2) (A 1 2) (B 1 2)]
      exact associator_swap_first (A 1 2) (B 1 2) ((A * A) 1 2)
    simp only [fa, fb, fd, fe, ff, fg, fh, fi, fj]
    abel
  have hN : A * (A * A) - A * A * A = -associator A A A := by unfold associator; abel
  have hcomm : (B * (A * (A * A) - A * A * A)) 1 2 - ((A * (A * A) - A * A * A) * B) 1 2
      = (2 : ℕ) • (associator (A 1 2) (A 2 0) (A 0 1) * B 1 2
        - B 1 2 * associator (A 1 2) (A 2 0) (A 0 1)) := by
    rw [hN]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.neg_apply]
    rw [matrix_associator_offdiag12_self A hA, matrix_associator_offdiag02_self A hA,
      matrix_associator_offdiag10_self A hA,
      matrix_associator_diag2_self A hA, matrix_associator_diag1_self A hA, two_smul]
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_add, mul_neg, neg_mul]
    rw [show associator (A 2 0) (A 0 1) (A 1 2) = associator (A 1 2) (A 2 0) (A 0 1) from
      (associator_cyclic (A 1 2) (A 2 0) (A 0 1)).symm]
    simp only [smul_mul_assoc]
    abel
  have t12 : associator (B 1 2) (A 1 2) ((A * A) 1 2) + associator (B 1 2) (A 2 0) ((A * A) 2 0)
      + associator (B 1 2) (A 0 1) ((A * A) 0 1)
      + (B 1 2 * associator (A 1 2) (A 2 0) (A 0 1) - associator (A 1 2) (A 2 0) (A 0 1) * B 1 2)
      = 0 := by
    have hA00 : IsNuclear (A 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 0 0)
    have hA11 : IsNuclear (A 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 1 1)
    have hA22 : IsNuclear (A 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 2 2)
    have r1 : associator (B 1 2) (A 1 2) ((A * A) 1 2)
        = associator (B 1 2) (A 1 2) (A 1 0 * A 0 2) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      rw [associator_add_right, associator_add_right,
        nuclear_slip_last hA11 (B 1 2) (A 1 2) (A 1 2),
        nuclear_slip_last_right hA22 (B 1 2) (A 1 2) (A 1 2),
        associator_right_self (A 1 2) (B 1 2), mul_zero, zero_mul]
      abel
    have r2 : associator (B 1 2) (A 2 0) ((A * A) 2 0)
        = associator (B 1 2) (A 2 0) (A 2 1 * A 1 0) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      rw [associator_add_right, associator_add_right,
        nuclear_slip_last_right hA00 (B 1 2) (A 2 0) (A 2 0),
        nuclear_slip_last hA22 (B 1 2) (A 2 0) (A 2 0),
        associator_right_self (A 2 0) (B 1 2), mul_zero, zero_mul]
      abel
    have r3 : associator (B 1 2) (A 0 1) ((A * A) 0 1)
        = associator (B 1 2) (A 0 1) (A 0 2 * A 2 1) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      rw [associator_add_right, associator_add_right,
        nuclear_slip_last hA00 (B 1 2) (A 0 1) (A 0 1),
        nuclear_slip_last_right hA11 (B 1 2) (A 0 1) (A 0 1),
        associator_right_self (A 0 1) (B 1 2), mul_zero, zero_mul]
      abel
    rw [r1, r2, r3]
    have e1 : A 0 2 * A 2 1 = star (A 1 2 * A 2 0) := by
      rw [star_mul, ← hA.apply 2 0, ← hA.apply 1 2, star_star, star_star]
    have e2 : A 1 0 * A 0 2 = star (A 2 0 * A 0 1) := by
      rw [star_mul, ← hA.apply 0 1, ← hA.apply 2 0, star_star, star_star]
    have e3 : A 2 1 * A 1 0 = star (A 0 1 * A 1 2) := by
      rw [star_mul, ← hA.apply 1 2, ← hA.apply 0 1, star_star, star_star]
    rw [e2, e3, e1, assoc_star_last, assoc_star_last, assoc_star_last]
    have key := mccrimmon_key_identity (B 1 2) (A 1 2) (A 2 0) (A 0 1)
    linear_combination (norm := abel) key
  linear_combination (norm := abel) pos - neg + hcomm - 2 • t12

/-- The `(0,2)` analogue of `hermitian_jordan_offdiag01` -- genuinely different from the `(1,2)`
case above, not reachable by the same cyclic shift (`(0,2)` isn't in the `(0,1)→(1,2)→(2,0)` shift
orbit). The key difference from both `offdiag01`/`offdiag12`: in `t02`'s per-entry reduction
(`r1`/`r2`/`r3`), the Hermitian conversion needed is on the associator's *second* argument (via
`assoc_star_mid`, converting e.g. `A 0 2` to `star (A 2 0)`) rather than a *product* sitting in the
third argument (via `assoc_star_last`, as in `offdiag01`/`offdiag12`'s `t01`/`t12`) -- which
`assoc_star_first/mid/last` slot is needed depends on which side of the "positive/negative sum"
split each surviving term's Hermitian-conjugate partner happens to land on for this particular
position, not something derivable in advance without doing the computation. -/
theorem hermitian_jordan_offdiag02 (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)) 0 2 = 0 := by
  have hC : (A * A).IsHermitian := hermitian_sq hA
  have h02 := congrFun (congrFun (plus_associator_eq A B (A * A)) 0) 2
  rw [h02]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have pos : associator A B (A * A) 0 2 + associator B A (A * A) 0 2
      + associator A (A * A) B 0 2 =
      -(associator (B 0 2) (A 0 2) ((A * A) 0 2) + associator (B 0 2) (A 2 1) ((A * A) 2 1)
        + associator (B 0 2) (A 1 0) ((A * A) 1 0)) := by
    rw [matrix_associator_offdiag02 A B (A * A) hA hB hC,
      matrix_associator_offdiag02 B A (A * A) hB hA hC,
      matrix_associator_offdiag02 A (A * A) B hA hC hB]
    have s1 : associator (A 0 2) (B 0 2) ((A * A) 0 2)
        = -associator (B 0 2) (A 0 2) ((A * A) 0 2) :=
      associator_swap_first (A 0 2) (B 0 2) ((A * A) 0 2)
    have s2 : associator (A 0 2) ((A * A) 0 2) (B 0 2)
        = -associator (A 0 2) (B 0 2) ((A * A) 0 2) := by
      linear_combination (norm := abel) associator_swap_last (A 0 2) (B 0 2) ((A * A) 0 2)
    have s3 : associator (A 0 2) ((A * A) 2 1) (B 2 1)
        = -associator (A 0 2) (B 2 1) ((A * A) 2 1) := by
      linear_combination (norm := abel) associator_swap_last (A 0 2) (B 2 1) ((A * A) 2 1)
    have s4 : associator (B 1 0) (A 1 0) ((A * A) 0 2)
        = -associator (A 1 0) (B 1 0) ((A * A) 0 2) :=
      associator_swap_first (B 1 0) (A 1 0) ((A * A) 0 2)
    have s5 : associator (A 1 0) ((A * A) 1 0) (B 0 2)
        = associator (B 0 2) (A 1 0) ((A * A) 1 0) :=
      (associator_cyclic (A 1 0) ((A * A) 1 0) (B 0 2)).trans
        (associator_cyclic ((A * A) 1 0) (B 0 2) (A 1 0))
    simp only [s1, s2, s3, s4, s5]
    abel
  have neg : associator (A * A) B A 0 2 + associator (A * A) A B 0 2
      + associator B (A * A) A 0 2 =
      associator (B 0 2) (A 0 2) ((A * A) 0 2) + associator (B 0 2) (A 2 1) ((A * A) 2 1)
        + associator (B 0 2) (A 1 0) ((A * A) 1 0) := by
    rw [matrix_associator_offdiag02 (A * A) B A hC hB hA,
      matrix_associator_offdiag02 (A * A) A B hC hA hB,
      matrix_associator_offdiag02 B (A * A) A hB hC hA]
    have fa : associator ((A * A) 0 2) (B 0 2) (A 0 2)
        = -associator ((A * A) 0 2) (A 0 2) (B 0 2) :=
      associator_swap_last ((A * A) 0 2) (B 0 2) (A 0 2)
    have fb : associator (B 0 2) ((A * A) 0 2) (A 0 2)
        = -associator ((A * A) 0 2) (B 0 2) (A 0 2) :=
      associator_swap_first (B 0 2) ((A * A) 0 2) (A 0 2)
    have fd : associator ((A * A) 0 2) (B 2 1) (A 2 1)
        = -associator ((A * A) 0 2) (A 2 1) (B 2 1) :=
      associator_swap_last ((A * A) 0 2) (B 2 1) (A 2 1)
    have fe : associator (B 0 2) ((A * A) 2 1) (A 2 1)
        = -associator (B 0 2) (A 2 1) ((A * A) 2 1) :=
      associator_swap_last (B 0 2) ((A * A) 2 1) (A 2 1)
    have ff : associator ((A * A) 1 0) (B 1 0) (A 0 2)
        = -associator (B 1 0) ((A * A) 1 0) (A 0 2) :=
      associator_swap_first ((A * A) 1 0) (B 1 0) (A 0 2)
    have fg : associator ((A * A) 1 0) (A 1 0) (B 0 2)
        = associator (A 1 0) (B 0 2) ((A * A) 1 0) :=
      associator_cyclic ((A * A) 1 0) (A 1 0) (B 0 2)
    have fh : associator (A 1 0) (B 0 2) ((A * A) 1 0)
        = associator (B 0 2) ((A * A) 1 0) (A 1 0) :=
      associator_cyclic (A 1 0) (B 0 2) ((A * A) 1 0)
    have fi : associator (B 0 2) ((A * A) 1 0) (A 1 0)
        = -associator (B 0 2) (A 1 0) ((A * A) 1 0) :=
      associator_swap_last (B 0 2) ((A * A) 1 0) (A 1 0)
    have fj : associator ((A * A) 0 2) (A 0 2) (B 0 2)
        = -associator (B 0 2) (A 0 2) ((A * A) 0 2) := by
      rw [associator_cyclic ((A * A) 0 2) (A 0 2) (B 0 2)]
      exact associator_swap_first (A 0 2) (B 0 2) ((A * A) 0 2)
    simp only [fa, fb, fd, fe, ff, fg, fh, fi, fj]
    abel
  have hN : A * (A * A) - A * A * A = -associator A A A := by unfold associator; abel
  have hcomm : (B * (A * (A * A) - A * A * A)) 0 2 - ((A * (A * A) - A * A * A) * B) 0 2
      = (2 : ℕ) • (associator (A 0 1) (A 1 2) (A 2 0) * B 0 2
        - B 0 2 * associator (A 0 1) (A 1 2) (A 2 0)) := by
    rw [hN]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.neg_apply]
    rw [matrix_associator_offdiag02_self A hA, matrix_associator_offdiag12_self A hA,
      matrix_associator_offdiag01_self A hA,
      matrix_associator_diag0_self A hA, matrix_associator_diag2_self A hA, two_smul,
      associator_cyclic (A 2 0) (A 0 1) (A 1 2)]
    simp only [mul_zero, zero_mul, neg_zero, add_zero, mul_add, mul_neg, neg_mul]
    simp only [smul_mul_assoc]
    abel
  have t02 : associator (B 0 2) (A 0 2) ((A * A) 0 2) + associator (B 0 2) (A 2 1) ((A * A) 2 1)
      + associator (B 0 2) (A 1 0) ((A * A) 1 0)
      + (B 0 2 * associator (A 0 1) (A 1 2) (A 2 0) - associator (A 0 1) (A 1 2) (A 2 0) * B 0 2)
      = 0 := by
    have hA00 : IsNuclear (A 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 0 0)
    have hA11 : IsNuclear (A 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 1 1)
    have hA22 : IsNuclear (A 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 2 2)
    have r1 : associator (B 0 2) (A 0 2) ((A * A) 0 2)
        = -associator (B 0 2) (A 2 0) (A 0 1 * A 1 2) := by
      have raw : associator (B 0 2) (A 0 2) ((A * A) 0 2)
          = associator (B 0 2) (A 0 2) (A 0 1 * A 1 2) := by
        simp only [Matrix.mul_apply, Fin.sum_univ_three]
        rw [associator_add_right, associator_add_right,
          nuclear_slip_last hA00 (B 0 2) (A 0 2) (A 0 2),
          nuclear_slip_last_right hA22 (B 0 2) (A 0 2) (A 0 2),
          associator_right_self (A 0 2) (B 0 2), mul_zero, zero_mul]
        abel
      rw [raw, show A 0 2 = star (A 2 0) from (hA.apply 0 2).symm, assoc_star_mid]
    have r2 : associator (B 0 2) (A 2 1) ((A * A) 2 1)
        = -associator (B 0 2) (A 1 2) (A 2 0 * A 0 1) := by
      have raw : associator (B 0 2) (A 2 1) ((A * A) 2 1)
          = associator (B 0 2) (A 2 1) (A 2 0 * A 0 1) := by
        simp only [Matrix.mul_apply, Fin.sum_univ_three]
        rw [associator_add_right, associator_add_right,
          nuclear_slip_last hA22 (B 0 2) (A 2 1) (A 2 1),
          nuclear_slip_last_right hA11 (B 0 2) (A 2 1) (A 2 1),
          associator_right_self (A 2 1) (B 0 2), mul_zero, zero_mul]
        abel
      rw [raw, show A 2 1 = star (A 1 2) from (hA.apply 2 1).symm, assoc_star_mid]
    have r3 : associator (B 0 2) (A 1 0) ((A * A) 1 0)
        = -associator (B 0 2) (A 0 1) (A 1 2 * A 2 0) := by
      have raw : associator (B 0 2) (A 1 0) ((A * A) 1 0)
          = associator (B 0 2) (A 1 0) (A 1 2 * A 2 0) := by
        simp only [Matrix.mul_apply, Fin.sum_univ_three]
        rw [associator_add_right, associator_add_right,
          nuclear_slip_last_right hA00 (B 0 2) (A 1 0) (A 1 0),
          nuclear_slip_last hA11 (B 0 2) (A 1 0) (A 1 0),
          associator_right_self (A 1 0) (B 0 2), mul_zero, zero_mul]
        abel
      rw [raw, show A 1 0 = star (A 0 1) from (hA.apply 1 0).symm, assoc_star_mid]
    rw [r1, r2, r3]
    have key := mccrimmon_key_identity (B 0 2) (A 0 1) (A 1 2) (A 2 0)
    linear_combination (norm := abel) key
  linear_combination (norm := abel) pos - neg + hcomm - 2 • t02

/-- **McCrimmon's `3x3` Coordinate Theorem C.1.3, in full**: the Jordan identity `[A,B,A^2]+ = 0`
for Hermitian `A B` over an alternative coordinate ring `D` with nuclear involution. Assembled from
the six per-position theorems above, plus one more generic fact proved inline: `[A,B,A^2]+` is
itself always Hermitian (a short computation via `Matrix.conjTranspose_add/sub/mul` and `hA.eq`/
`hB.eq`), which gives the `(1,0)`/`(2,0)`/`(2,1)` entries for free from
`offdiag01`/`offdiag02`/`offdiag12` via `star 0 = 0` -- no need to redo the harder off-diagonal
derivation a fourth, fifth, and sixth time. -/
theorem hermitian_jordan_identity (A B : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    (A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A) = 0 := by
  have hHerm : ((A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A)).IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]
    rw [hA.eq, hB.eq]
    abel_nf
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply]
  · exact hermitian_jordan_diag0 A B hA hB
  · exact hermitian_jordan_offdiag01 A B hA hB
  · exact hermitian_jordan_offdiag02 A B hA hB
  · have h := hHerm.apply 1 0
    rw [hermitian_jordan_offdiag01 A B hA hB] at h
    simpa using h.symm
  · exact hermitian_jordan_diag1 A B hA hB
  · exact hermitian_jordan_offdiag12 A B hA hB
  · have h := hHerm.apply 2 0
    rw [hermitian_jordan_offdiag02 A B hA hB] at h
    simpa using h.symm
  · have h := hHerm.apply 2 1
    rw [hermitian_jordan_offdiag12 A B hA hB] at h
    simpa using h.symm
  · exact hermitian_jordan_diag2 A B hA hB
