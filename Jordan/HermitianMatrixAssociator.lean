import Jordan.MatrixAssociator
import Jordan.NuclearInvolution
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The matrix associator for Hermitian `3 x 3` matrices

McCrimmon's Matrix Associator Facts (*A Taste of Jordan Algebras*, Appendix C.1, Lemma C.1.2,
(1.2.1)-(1.2.4)): for Hermitian `3 x 3` matrices `A B C` over a coordinate ring `D` with a nuclear
involution (`Jordan.NuclearInvolution`), the double-sum reduction `matrix_associator_apply` (from
`Jordan.MatrixAssociator`) collapses further, since associators touching a diagonal (hence
star-fixed, hence nuclear) entry vanish, and a lower-triangular entry can be traded for minus its
upper-triangular partner (`assoc_star_first/mid/last`). This isolates:

* **diagonal** entries (1.2.1): `[A,B,C]_rr` down to the two associators built from the *other*
  two matrix positions in each cyclic order;
* **off-diagonal** entries (1.2.3): `[A,B,C]_rs` down to three associators, each involving only
  the `(r,s)`-adjacent positions.

(1.2.2)/(1.2.4) are the `B = C = A` specializations of each, used later to verify the Jordan
identity `[A,B,A^2] = 0`-style computations for `H_3(D,-)`. Stated concretely for each of the
three matrix positions (`0/1/2` diagonal, `(0,1)/(0,2)/(1,2)` off-diagonal) rather than
parametrized over `Fin 3` -- `fin_cases`-driven unification hit `Fin.mk`-vs-numeral normalization
friction that wasn't worth fighting for a three-case split; this also matches the existing
`jordan_case_diag0/1/2`/`jordan_case_off01/02/12` convention already used in `AlbertAlgebra.lean`.
See `JORDAN_IDENTITY_PLAN.md`.
-/

open IsAlternative

variable {D : Type*} [NonUnitalNonAssocRing D] [IsAlternative D] [StarAddMonoid D]
  [IsNuclearInvolution D]

/-- **McCrimmon's (1.2.1)**, `r = 0` case: the `(0,0)` diagonal entry of the matrix associator
reduces to the two associators built from the `(0,1)`, `(1,2)`, `(2,0)` positions, in each cyclic
order. -/
theorem matrix_associator_diag0 (A B C : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    associator A B C 0 0
      = associator (A 0 1) (B 1 2) (C 2 0) + associator (C 0 1) (B 1 2) (A 2 0) := by
  have hA00 : IsNuclear (A 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 0 0)
  have hB11 : IsNuclear (B 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 1 1)
  have hB22 : IsNuclear (B 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 2 2)
  have hC00 : IsNuclear (C 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hC.apply 0 0)
  have hterm8 : associator (A 0 2) (B 2 1) (C 1 0) = associator (C 0 1) (B 1 2) (A 2 0) := by
    rw [show B 2 1 = star (B 1 2) from (hB.apply 2 1).symm,
      show C 1 0 = star (C 0 1) from (hC.apply 1 0).symm,
      show A 2 0 = star (A 0 2) from (hA.apply 2 0).symm]
    simp only [assoc_star_mid, assoc_star_last]
    linear_combination (norm := abel) associator_swap_outer (A 0 2) (B 1 2) (C 0 1)
  rw [matrix_associator_apply]
  simp only [Fin.sum_univ_three]
  rw [(hA00 (B 0 0) (C 0 0)).1, (hA00 (B 0 1) (C 1 0)).1, (hA00 (B 0 2) (C 2 0)).1,
    (hC00 (A 0 1) (B 1 0)).2.2, (hB11 (A 0 1) (C 1 0)).2.1,
    (hC00 (A 0 2) (B 2 0)).2.2, (hB22 (A 0 2) (C 2 0)).2.1, hterm8]
  abel

/-- The `1`-diagonal analogue of `matrix_associator_diag0`. -/
theorem matrix_associator_diag1 (A B C : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    associator A B C 1 1
      = associator (A 1 2) (B 2 0) (C 0 1) + associator (C 1 2) (B 2 0) (A 0 1) := by
  have hA11 : IsNuclear (A 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 1 1)
  have hB22 : IsNuclear (B 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 2 2)
  have hB00 : IsNuclear (B 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 0 0)
  have hC11 : IsNuclear (C 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hC.apply 1 1)
  have hterm8 : associator (A 1 0) (B 0 2) (C 2 1) = associator (C 1 2) (B 2 0) (A 0 1) := by
    rw [show B 0 2 = star (B 2 0) from (hB.apply 0 2).symm,
      show C 2 1 = star (C 1 2) from (hC.apply 2 1).symm,
      show A 0 1 = star (A 1 0) from (hA.apply 0 1).symm]
    simp only [assoc_star_mid, assoc_star_last]
    linear_combination (norm := abel) associator_swap_outer (A 1 0) (B 2 0) (C 1 2)
  rw [matrix_associator_apply]
  simp only [Fin.sum_univ_three]
  rw [(hA11 (B 1 1) (C 1 1)).1, (hA11 (B 1 2) (C 2 1)).1, (hA11 (B 1 0) (C 0 1)).1,
    (hC11 (A 1 2) (B 2 1)).2.2, (hB22 (A 1 2) (C 2 1)).2.1,
    (hC11 (A 1 0) (B 0 1)).2.2, (hB00 (A 1 0) (C 0 1)).2.1, hterm8]
  abel

/-- The `2`-diagonal analogue of `matrix_associator_diag0`. -/
theorem matrix_associator_diag2 (A B C : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    associator A B C 2 2
      = associator (A 2 0) (B 0 1) (C 1 2) + associator (C 2 0) (B 0 1) (A 1 2) := by
  have hA22 : IsNuclear (A 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 2 2)
  have hB00 : IsNuclear (B 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 0 0)
  have hB11 : IsNuclear (B 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 1 1)
  have hC22 : IsNuclear (C 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hC.apply 2 2)
  have hterm8 : associator (A 2 1) (B 1 0) (C 0 2) = associator (C 2 0) (B 0 1) (A 1 2) := by
    rw [show B 1 0 = star (B 0 1) from (hB.apply 1 0).symm,
      show C 0 2 = star (C 2 0) from (hC.apply 0 2).symm,
      show A 1 2 = star (A 2 1) from (hA.apply 1 2).symm]
    simp only [assoc_star_mid, assoc_star_last]
    linear_combination (norm := abel) associator_swap_outer (A 2 1) (B 0 1) (C 2 0)
  rw [matrix_associator_apply]
  simp only [Fin.sum_univ_three]
  rw [(hA22 (B 2 2) (C 2 2)).1, (hA22 (B 2 0) (C 0 2)).1, (hA22 (B 2 1) (C 1 2)).1,
    (hC22 (A 2 0) (B 0 2)).2.2, (hB00 (A 2 0) (C 0 2)).2.1,
    (hC22 (A 2 1) (B 1 2)).2.2, (hB11 (A 2 1) (C 1 2)).2.1, hterm8]
  abel

/-- **McCrimmon's (1.2.2)**, `r = 0` case (the `A = B = C` specialization of `matrix_associator_diag0`):
`[A,A,A]_00 = 2 * [a01,a12,a20]`. -/
theorem matrix_associator_diag0_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 0 0 = 2 • associator (A 0 1) (A 1 2) (A 2 0) := by
  rw [matrix_associator_diag0 A A A hA hA hA, two_smul]

/-- The `r = 1` analogue of `matrix_associator_diag0_self`. -/
theorem matrix_associator_diag1_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 1 1 = 2 • associator (A 1 2) (A 2 0) (A 0 1) := by
  rw [matrix_associator_diag1 A A A hA hA hA, two_smul]

/-- The `r = 2` analogue of `matrix_associator_diag0_self`. -/
theorem matrix_associator_diag2_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 2 2 = 2 • associator (A 2 0) (A 0 1) (A 1 2) := by
  rw [matrix_associator_diag2 A A A hA hA hA, two_smul]

/-- **McCrimmon's (1.2.3)**, `(r,s) = (0,1)` case: the `(0,1)` off-diagonal entry of the matrix
associator reduces to (minus) three associators, each built from the `(0,1)`/`(1,2)`/`(2,0)`
positions "adjacent" to `(0,1)`. -/
theorem matrix_associator_offdiag01 (A B C : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    associator A B C 0 1 =
      -associator (A 0 1) (B 0 1) (C 0 1) - associator (A 0 1) (B 1 2) (C 1 2)
        - associator (A 2 0) (B 2 0) (C 0 1) := by
  have hA00 : IsNuclear (A 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 0 0)
  have hB22 : IsNuclear (B 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 2 2)
  have hC11 : IsNuclear (C 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hC.apply 1 1)
  have h1 : associator (A 0 1) (B 1 0) (C 0 1) = -associator (A 0 1) (B 0 1) (C 0 1) := by
    rw [show B 1 0 = star (B 0 1) from (hB.apply 1 0).symm, assoc_star_mid]
  have h2 : associator (A 0 1) (B 1 2) (C 2 1) = -associator (A 0 1) (B 1 2) (C 1 2) := by
    rw [show C 2 1 = star (C 1 2) from (hC.apply 2 1).symm, assoc_star_last]
  have h3 : associator (A 0 2) (B 2 0) (C 0 1) = -associator (A 2 0) (B 2 0) (C 0 1) := by
    rw [show A 0 2 = star (A 2 0) from (hA.apply 0 2).symm, assoc_star_first]
  rw [matrix_associator_apply]
  simp only [Fin.sum_univ_three]
  rw [(hA00 (B 0 0) (C 0 1)).1, (hA00 (B 0 1) (C 1 1)).1, (hA00 (B 0 2) (C 2 1)).1,
    (hC11 (A 0 1) (B 1 1)).2.2, (hC11 (A 0 2) (B 2 1)).2.2, (hB22 (A 0 2) (C 2 1)).2.1,
    h1, h2, h3]
  abel

/-- The `(0,2)` analogue of `matrix_associator_offdiag01`. -/
theorem matrix_associator_offdiag02 (A B C : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    associator A B C 0 2 =
      -associator (A 0 2) (B 0 2) (C 0 2) - associator (A 0 2) (B 2 1) (C 2 1)
        - associator (A 1 0) (B 1 0) (C 0 2) := by
  have hA00 : IsNuclear (A 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 0 0)
  have hB11 : IsNuclear (B 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 1 1)
  have hC22 : IsNuclear (C 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hC.apply 2 2)
  have h1 : associator (A 0 2) (B 2 0) (C 0 2) = -associator (A 0 2) (B 0 2) (C 0 2) := by
    rw [show B 2 0 = star (B 0 2) from (hB.apply 2 0).symm, assoc_star_mid]
  have h2 : associator (A 0 2) (B 2 1) (C 1 2) = -associator (A 0 2) (B 2 1) (C 2 1) := by
    rw [show C 1 2 = star (C 2 1) from (hC.apply 1 2).symm, assoc_star_last]
  have h3 : associator (A 0 1) (B 1 0) (C 0 2) = -associator (A 1 0) (B 1 0) (C 0 2) := by
    rw [show A 0 1 = star (A 1 0) from (hA.apply 0 1).symm, assoc_star_first]
  rw [matrix_associator_apply]
  simp only [Fin.sum_univ_three]
  rw [(hA00 (B 0 0) (C 0 2)).1, (hA00 (B 0 1) (C 1 2)).1, (hA00 (B 0 2) (C 2 2)).1,
    (hB11 (A 0 1) (C 1 2)).2.1, (hC22 (A 0 1) (B 1 2)).2.2, (hC22 (A 0 2) (B 2 2)).2.2,
    h1, h2, h3]
  abel

/-- The `(1,2)` analogue of `matrix_associator_offdiag01`. -/
theorem matrix_associator_offdiag12 (A B C : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    associator A B C 1 2 =
      -associator (A 1 2) (B 1 2) (C 1 2) - associator (A 1 2) (B 2 0) (C 2 0)
        - associator (A 0 1) (B 0 1) (C 1 2) := by
  have hA11 : IsNuclear (A 1 1) := IsNuclearInvolution.isNuclear_of_star_eq _ (hA.apply 1 1)
  have hB00 : IsNuclear (B 0 0) := IsNuclearInvolution.isNuclear_of_star_eq _ (hB.apply 0 0)
  have hC22 : IsNuclear (C 2 2) := IsNuclearInvolution.isNuclear_of_star_eq _ (hC.apply 2 2)
  have h1 : associator (A 1 2) (B 2 1) (C 1 2) = -associator (A 1 2) (B 1 2) (C 1 2) := by
    rw [show B 2 1 = star (B 1 2) from (hB.apply 2 1).symm, assoc_star_mid]
  have h2 : associator (A 1 2) (B 2 0) (C 0 2) = -associator (A 1 2) (B 2 0) (C 2 0) := by
    rw [show C 0 2 = star (C 2 0) from (hC.apply 0 2).symm, assoc_star_last]
  have h3 : associator (A 1 0) (B 0 1) (C 1 2) = -associator (A 0 1) (B 0 1) (C 1 2) := by
    rw [show A 1 0 = star (A 0 1) from (hA.apply 1 0).symm, assoc_star_first]
  rw [matrix_associator_apply]
  simp only [Fin.sum_univ_three]
  rw [(hA11 (B 1 1) (C 1 2)).1, (hA11 (B 1 2) (C 2 2)).1, (hA11 (B 1 0) (C 0 2)).1,
    (hB00 (A 1 0) (C 0 2)).2.1, (hC22 (A 1 0) (B 0 2)).2.2, (hC22 (A 1 2) (B 2 2)).2.2,
    h1, h2, h3]
  abel

/-- **McCrimmon's (1.2.4)**, `(0,1)` case (the `A = B = C` specialization of
`matrix_associator_offdiag01`): `[A,A,A]_01 = 0`, since each of the three surviving associators has
a repeated argument and vanishes by `associator_self_left`/`associator_right_self`. -/
theorem matrix_associator_offdiag01_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 0 1 = 0 := by
  rw [matrix_associator_offdiag01 A A A hA hA hA,
    associator_self_left (A 0 1) (A 0 1),
    associator_right_self (A 1 2) (A 0 1),
    associator_self_left (A 2 0) (A 0 1)]
  abel

/-- The `(0,2)` analogue of `matrix_associator_offdiag01_self`. -/
theorem matrix_associator_offdiag02_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 0 2 = 0 := by
  rw [matrix_associator_offdiag02 A A A hA hA hA,
    associator_self_left (A 0 2) (A 0 2),
    associator_right_self (A 2 1) (A 0 2),
    associator_self_left (A 1 0) (A 0 2)]
  abel

/-- The `(1,2)` analogue of `matrix_associator_offdiag01_self`. -/
theorem matrix_associator_offdiag12_self (A : Matrix (Fin 3) (Fin 3) D) (hA : A.IsHermitian) :
    associator A A A 1 2 = 0 := by
  rw [matrix_associator_offdiag12 A A A hA hA hA,
    associator_self_left (A 1 2) (A 1 2),
    associator_right_self (A 2 0) (A 1 2),
    associator_self_left (A 0 1) (A 1 2)]
  abel
