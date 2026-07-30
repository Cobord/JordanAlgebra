import Jordan.Alternative
import Mathlib.Data.Matrix.Mul

/-!
# The matrix associator, entrywise

McCrimmon's Matrix Associator Fact (1.2.0) (*A Taste of Jordan Algebras*, Appendix C.1): for `n x
n` matrices `A B C` over *any* non-unital non-associative ring `D` (no associativity, no
alternativity, no Hermitian symmetry needed -- `Matrix n n D` is automatically a
`NonUnitalNonAssocRing` via `Matrix.nonUnitalNonAssocRing`, regardless of whether `D` itself is
associative), the matrix associator `IsAlternative.associator A B C` reduces entrywise to a double
sum of `D`'s own associator. This is the fully generic ingredient behind McCrimmon's Matrix
Associator Facts (1.2.1)-(1.2.4), which further specialize this to `n = 3` and Hermitian `A B C`
(using that diagonal entries are central/nuclear) -- see `JORDAN_IDENTITY_PLAN.md`. Those
specializations belong with the `AlbertAlgebra` development, not here; this file only has the
part that's uniform over every coordinate ring `D` and every matrix size `n`.
-/

open IsAlternative

variable {D : Type*} [NonUnitalNonAssocRing D] {n : Type*} [Fintype n]

/-- **McCrimmon's (1.2.0)**: the `(r,s)`-entry of the matrix associator `(A,B,C)` of `n x n`
matrices over any non-unital non-associative ring `D` equals `∑ j k, associator (A r j) (B j k)
(C k s)`, the double sum of `D`'s own associator over the two "internal" matrix indices `j, k`. -/
theorem matrix_associator_apply (A B C : Matrix n n D) (r s : n) :
    associator A B C r s = ∑ j, ∑ k, associator (A r j) (B j k) (C k s) := by
  unfold associator
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext j
  rw [← Finset.sum_sub_distrib]
