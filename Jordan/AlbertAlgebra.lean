import Mathlib.Tactic.LinearCombination
import Jordan.HermitianMatrixJordanIdentity
import Jordan.Octonion
import Jordan.OctonionMatrix

open scoped Quaternion

/-!
# The exceptional Jordan algebra (Albert algebra)

The `3 x 3` Hermitian octonionic matrices, `H_3(O)`. Unlike the `1 x 1`/`2 x 2` cases in
`Jordan.OctonionMatrix`, `HermitianJordan.ofInvolutiveAlgebra` does not apply here, since the
ambient octonion matrix algebra is not associative: proving `AlbertAlgebra` is actually a Jordan
algebra (`jordan_identity`) is the genuinely exceptional part of this construction.
-/

namespace Octonion

section ThreeByThree

variable {R : Type*}
variable [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

abbrev AlbertAlgebra := HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 3)

/-- Build a `3 x 3` Hermitian octonionic matrix from its three (real) diagonal entries and its
three upper off-diagonal octonion entries -- the `3 x 3` analogue of `buildTwo`. -/
private def buildThree (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 3) :=
  !![Octonion.scalarEmbed r0, x01, x02;
     star x01, Octonion.scalarEmbed r1, x12;
     star x02, star x12, Octonion.scalarEmbed r2]

omit i2 in
private lemma buildThree_isHermitian (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    star (buildThree (R:=R) (a:=a) (b:=b) (c:=c) r0 r1 r2 x01 x02 x12) =
      buildThree r0 r1 r2 x01 x02 x12 := by
  apply Matrix.ext
  intro i j
  show star (buildThree r0 r1 r2 x01 x02 x12 j i) = buildThree r0 r1 r2 x01 x02 x12 i j
  fin_cases i <;> fin_cases j <;>
    simp [buildThree, Octonion.star_scalarEmbed, star_star]

private def buildThreeH (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  ⟨buildThree r0 r1 r2 x01 x02 x12, buildThree_isHermitian r0 r1 r2 x01 x02 x12⟩

/-- The (real) `i`-th diagonal entry of a Hermitian `3 x 3` octonionic matrix, read off via the
quaternion real-part coordinate, the `3 x 3` analogue of `HermitianOctonionMatrixTwo.traceHalf`/
`diffHalf` (but a single raw diagonal entry, with no half-sum/half-difference reparametrization
needed since here it is paired with the *other two* diagonal entries, not folded into one). -/
private def HermitianOctonionMatrixThree.diagCoord
    (M : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) (i : Fin 3) : R :=
  (M.val i i).1.re

private lemma HermitianOctonionMatrixThree.diag_eq_scalarEmbed_diagCoord
    (M : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) (i : Fin 3) :
    M.val i i = Octonion.scalarEmbed (HermitianOctonionMatrixThree.diagCoord M i) := by
  obtain ⟨r, hr⟩ := diag_real M i
  have : HermitianOctonionMatrixThree.diagCoord M i = r := diag_just_11 (M.val i i) r hr
  rw [this, hr]

omit i2 in
/-- The off-diagonal Hermitian-symmetry conditions, the `3 x 3` analogue of
`HermitianOctonionMatrixTwo.off_diag`: in a Hermitian `3 x 3` octonionic matrix, each below-diagonal
entry is forced to be the conjugate of the corresponding above-diagonal entry. -/
private lemma HermitianOctonionMatrixThree.off_diag_10
    (M : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    M.val 1 0 = star (M.val 0 1) := by
  have h : star (M.val 1 0) = M.val 0 1 := congrFun (congrFun M.property 0) 1
  rw [← h, star_star]

omit i2 in
private lemma HermitianOctonionMatrixThree.off_diag_20
    (M : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    M.val 2 0 = star (M.val 0 2) := by
  have h : star (M.val 2 0) = M.val 0 2 := congrFun (congrFun M.property 0) 2
  rw [← h, star_star]

omit i2 in
private lemma HermitianOctonionMatrixThree.off_diag_21
    (M : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    M.val 2 1 = star (M.val 1 2) := by
  have h : star (M.val 2 1) = M.val 1 2 := congrFun (congrFun M.property 1) 2
  rw [← h, star_star]

/-- Every Hermitian `3 x 3` octonionic matrix is recovered from `buildThree` applied to its own
diagonal coordinates and upper off-diagonal entries -- the `3 x 3` analogue of
`HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf` composed with `buildTwo`, but
stated directly as a round-trip identity so it can double as the `left_inv` field of `albertEquiv`
below and as the decomposition step in `jordan_identity`. -/
private lemma HermitianOctonionMatrixThree.eq_buildThreeH
    (M : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    M = buildThreeH (HermitianOctonionMatrixThree.diagCoord M 0)
      (HermitianOctonionMatrixThree.diagCoord M 1) (HermitianOctonionMatrixThree.diagCoord M 2)
      (M.val 0 1) (M.val 0 2) (M.val 1 2) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  show M.val i j =
    buildThree (HermitianOctonionMatrixThree.diagCoord M 0)
      (HermitianOctonionMatrixThree.diagCoord M 1) (HermitianOctonionMatrixThree.diagCoord M 2)
      (M.val 0 1) (M.val 0 2) (M.val 1 2) i j
  fin_cases i <;> fin_cases j
  · exact HermitianOctonionMatrixThree.diag_eq_scalarEmbed_diagCoord M 0
  · rfl
  · rfl
  · exact HermitianOctonionMatrixThree.off_diag_10 M
  · exact HermitianOctonionMatrixThree.diag_eq_scalarEmbed_diagCoord M 1
  · rfl
  · exact HermitianOctonionMatrixThree.off_diag_20 M
  · exact HermitianOctonionMatrixThree.off_diag_21 M
  · exact HermitianOctonionMatrixThree.diag_eq_scalarEmbed_diagCoord M 2

omit i2 in
private lemma HermitianOctonionMatrixThree.diagCoord_buildThreeH_0
    (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    HermitianOctonionMatrixThree.diagCoord (buildThreeH r0 r1 r2 x01 x02 x12) 0 = r0 :=
  diag_just_11 _ r0 rfl

omit i2 in
private lemma HermitianOctonionMatrixThree.diagCoord_buildThreeH_1
    (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    HermitianOctonionMatrixThree.diagCoord (buildThreeH r0 r1 r2 x01 x02 x12) 1 = r1 :=
  diag_just_11 _ r1 rfl

omit i2 in
private lemma HermitianOctonionMatrixThree.diagCoord_buildThreeH_2
    (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    HermitianOctonionMatrixThree.diagCoord (buildThreeH r0 r1 r2 x01 x02 x12) 2 = r2 :=
  diag_just_11 _ r2 rfl

/-- The decomposition of `AlbertAlgebra` as an `R`-module: it is `R`-linearly equivalent to three
copies of `R` (the diagonal entries) times three copies of `Octonion R a b c` (the upper
off-diagonal entries). This is *not* a ring isomorphism -- unlike `ofSymmetricMatricesTwo`, the
target carries no algebra structure matching the symmetrized matrix product, and none is claimed.
Its only jobs are: (1) exhibiting `AlbertAlgebra` as free (`albert_basis`), directly from
`Octonion`'s own freeness rather than any submodule-of-a-free-module-over-a-PID argument, which
`R` need not satisfy here; and (2) supplying the additive decomposition of an arbitrary `y` used to
reduce `jordan_identity`, linear in `y`, down to the six cases where `y` is a single diagonal or
off-diagonal generator. -/
noncomputable def albertEquiv :
    AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) ≃ₗ[R]
      (Fin 3 → R) × Octonion R a b c × Octonion R a b c × Octonion R a b c where
  toFun M := (fun i => HermitianOctonionMatrixThree.diagCoord M i, M.val 0 1, M.val 0 2, M.val 1 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := buildThreeH (p.1 0) (p.1 1) (p.1 2) p.2.1 p.2.2.1 p.2.2.2
  left_inv M := (HermitianOctonionMatrixThree.eq_buildThreeH M).symm
  right_inv p := by
    obtain ⟨f, x01, x02, x12⟩ := p
    apply Prod.ext
    · funext i
      fin_cases i
      · exact HermitianOctonionMatrixThree.diagCoord_buildThreeH_0 (f 0) (f 1) (f 2) x01 x02 x12
      · exact HermitianOctonionMatrixThree.diagCoord_buildThreeH_1 (f 0) (f 1) (f 2) x01 x02 x12
      · exact HermitianOctonionMatrixThree.diagCoord_buildThreeH_2 (f 0) (f 1) (f 2) x01 x02 x12
    · rfl

/-- `AlbertAlgebra` is a free `R`-module: transported from the freeness of
`(Fin 3 → R) × Octonion R a b c × Octonion R a b c × Octonion R a b c` (a finite product of free
modules, since `Octonion R a b c` is free) along `albertEquiv`. -/
lemma albert_basis : Module.Free R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :=
  Module.Free.of_equiv albertEquiv.symm

/-- The `3 x 3` Hermitian matrix with only the `0`-th diagonal entry nonzero. One of the six
"standard basis" generators used to reduce `jordan_identity` below. -/
private def diagPiece0 (r : R) : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  buildThreeH r 0 0 0 0 0

private def diagPiece1 (r : R) : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  buildThreeH 0 r 0 0 0 0

private def diagPiece2 (r : R) : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  buildThreeH 0 0 r 0 0 0

/-- The `3 x 3` Hermitian matrix with only the `(0,1)`/`(1,0)` off-diagonal entries nonzero (equal
to `x`/`star x`). One of the six "standard basis" generators used to reduce `jordan_identity`
below. -/
private def offPiece01 (x : Octonion R a b c) : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  buildThreeH 0 0 0 x 0 0

private def offPiece02 (x : Octonion R a b c) : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  buildThreeH 0 0 0 0 x 0

private def offPiece12 (x : Octonion R a b c) : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) :=
  buildThreeH 0 0 0 0 0 x

omit i2 in
/-- Every `buildThreeH` matrix splits additively into its six single-slot pieces: the three
diagonal entries and the three off-diagonal entries, each placed on its own. Since both sides of
`jordan_identity` are additive in `y` (the symmetrized product distributes over `+`), this is what
lets that identity -- a priori needing to be checked against a fully generic `y` -- be reduced to
checking it against each of these six generators (`jordan_case_diag0/1/2`, `jordan_case_off01/02/12`
below) instead, without needing to further expand the off-diagonal octonion entries `x01 x02 x12`
over any `R`-basis of `Octonion R a b c`. -/
private lemma buildThreeH_eq_sum (r0 r1 r2 : R) (x01 x02 x12 : Octonion R a b c) :
    buildThreeH r0 r1 r2 x01 x02 x12 =
      diagPiece0 r0 + diagPiece1 r1 + diagPiece2 r2 +
        offPiece01 x01 + offPiece02 x02 + offPiece12 x12 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [buildThreeH, buildThree, diagPiece0, diagPiece1, diagPiece2,
      offPiece01, offPiece02, offPiece12]

set_option linter.unreachableTactic false in
/-- `x ∘ (diagPiece0 ρ)` only touches row/column `0` of `x`: the diagonal entry there gets scaled
by `ρ`, the two off-diagonal entries touching it get scaled by `⅟2 * ρ`, and everything else
vanishes. Pure bookkeeping (`Matrix.mul_apply` plus `scalarEmbed`/`smul` identities), no
`IsAlternative` needed -- `diagPiece0 ρ` has only one nonzero entry, so no product of two distinct
off-diagonal entries of `x` can appear. -/
private lemma buildThreeH_mul_diagPiece0 (r0 r1 r2 ρ : R) (p q t : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * diagPiece0 ρ =
      buildThreeH (r0 * ρ) 0 0 ((⅟2 * ρ) • p) ((⅟2 * ρ) • q) 0 := by
  have hmul : (buildThreeH r0 r1 r2 p q t * diagPiece0 ρ).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree ρ 0 0 0 0 0 +
        buildThree ρ 0 0 0 0 0 * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;> simp <;>
    first
      | (rw [mul_scalarEmbed, scalarEmbed_mul, smul_smul, ← two_smul R, smul_smul]
         congr 1
         rw [← mul_assoc, mul_invOf_self, one_mul])
      | (rw [scalarEmbed_mul, smul_smul])
      | (rw [mul_scalarEmbed, smul_smul])

set_option linter.unreachableTactic false in
/-- The `diagPiece1` analogue of `buildThreeH_mul_diagPiece0`: `x ∘ (diagPiece1 ρ)` only touches
row/column `1` of `x`. -/
private lemma buildThreeH_mul_diagPiece1 (r0 r1 r2 ρ : R) (p q t : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * diagPiece1 ρ =
      buildThreeH 0 (r1 * ρ) 0 ((⅟2 * ρ) • p) 0 ((⅟2 * ρ) • t) := by
  have hmul : (buildThreeH r0 r1 r2 p q t * diagPiece1 ρ).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree 0 ρ 0 0 0 0 +
        buildThree 0 ρ 0 0 0 0 * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;> simp <;>
    first
      | (rw [mul_scalarEmbed, scalarEmbed_mul, smul_smul, ← two_smul R, smul_smul]
         congr 1
         rw [← mul_assoc, mul_invOf_self, one_mul])
      | (rw [scalarEmbed_mul, smul_smul])
      | (rw [mul_scalarEmbed, smul_smul])

set_option linter.unreachableTactic false in
/-- The `diagPiece2` analogue of `buildThreeH_mul_diagPiece0`: `x ∘ (diagPiece2 ρ)` only touches
row/column `2` of `x`. -/
private lemma buildThreeH_mul_diagPiece2 (r0 r1 r2 ρ : R) (p q t : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * diagPiece2 ρ =
      buildThreeH 0 0 (r2 * ρ) 0 ((⅟2 * ρ) • q) ((⅟2 * ρ) • t) := by
  have hmul : (buildThreeH r0 r1 r2 p q t * diagPiece2 ρ).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree 0 0 ρ 0 0 0 +
        buildThree 0 0 ρ 0 0 0 * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;> simp <;>
    first
      | (rw [mul_scalarEmbed, scalarEmbed_mul, smul_smul, ← two_smul R, smul_smul]
         congr 1
         rw [← mul_assoc, mul_invOf_self, one_mul])
      | (rw [scalarEmbed_mul, smul_smul])
      | (rw [mul_scalarEmbed, smul_smul])

omit i2 in
/-- `scalarEmbed` of the real part of `x * star x` is `x * star x` itself -- i.e. `x * star x` is
already exactly the scalar `mul_star_self_eq_scalarEmbed` says it is. Bridges the closed-form
`.1.re` expressions used in `buildThreeH_mul_self`'s diagonal entries back to the raw octonion
products that actually appear when expanding the matrix product. -/
private lemma scalarEmbed_mul_star_self_re (x : Octonion R a b c) :
    scalarEmbed ((x * star x).1.re) = x * star x := by
  rw [diag_just_11 (x * star x) _ (mul_star_self_eq_scalarEmbed x)]
  exact (mul_star_self_eq_scalarEmbed x).symm

omit i2 in
/-- The `star x * x` counterpart to `scalarEmbed_mul_star_self_re`. -/
private lemma scalarEmbed_star_mul_self_re (x : Octonion R a b c) :
    scalarEmbed ((star x * x).1.re) = star x * x := by
  rw [diag_just_11 (star x * x) _ (star_mul_self_eq_scalarEmbed x)]
  exact (star_mul_self_eq_scalarEmbed x).symm

set_option linter.unreachableTactic false in
/-- The Jordan square `x ∘ x = x * x` (the ordinary, not symmetrized, matrix square, since
symmetrizing a matrix against itself is a no-op) of a Hermitian `3 x 3` octonionic matrix, in terms
of its own six coordinates. The diagonal entries are genuine composition-algebra norms (central
scalars, via `mul_star_self_eq_scalarEmbed`/`star_mul_self_eq_scalarEmbed`); the off-diagonal
entries are left as raw octonion products of two of `x`'s own off-diagonal entries (e.g. `q * star
t` at `(0,1)`) -- these are exactly the cross terms `mul_mul_star_eq`/`star_mul_mul_eq` exist to
resolve, one step further down in `jordan_identity`, not here. -/
private lemma buildThreeH_mul_self (r0 r1 r2 : R) (p q t : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * buildThreeH r0 r1 r2 p q t =
      buildThreeH
        (r0 * r0 + (p * star p).1.re + (q * star q).1.re)
        (r1 * r1 + (star p * p).1.re + (t * star t).1.re)
        (r2 * r2 + (star q * q).1.re + (star t * t).1.re)
        ((r0 + r1) • p + q * star t)
        ((r0 + r2) • q + p * t)
        ((r1 + r2) • t + star p * q) := by
  have hval : (buildThreeH r0 r1 r2 p q t * buildThreeH r0 r1 r2 p q t).val =
      buildThree r0 r1 r2 p q t * buildThree r0 r1 r2 p q t := by
    show (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree r0 r1 r2 p q t +
      buildThree r0 r1 r2 p q t * buildThree r0 r1 r2 p q t) = _
    rw [← two_smul R, smul_smul, invOf_mul_self, one_smul]
  apply Subtype.ext
  rw [hval]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;>
    simp [-mul_fst, -mul_snd] <;>
    simp only [scalarEmbed_mul_star_self_re, scalarEmbed_star_mul_self_re, mul_scalarEmbed,
      scalarEmbed_mul] <;>
    module

/-- `scalarEmbed` of an `innerProduct` is exactly the polarized central scalar
`mul_star_add_star_mul_eq_scalarEmbed` produces, halved back down -- the bridge from the
closed-form `innerProduct` values used in `buildThreeH_mul_shape001`'s diagonal entries back to the
raw octonion sums that actually appear when expanding the matrix product (parallel to
`scalarEmbed_mul_star_self_re`/`scalarEmbed_star_mul_self_re` for `buildThreeH_mul_self`). -/
private lemma scalarEmbed_innerProduct_eq (x y : Octonion R a b c) :
    scalarEmbed (innerProduct x y) = (⅟2 : R) • (x * star y + y * star x) := by
  rw [mul_star_add_star_mul_eq_scalarEmbed, smul_scalarEmbed, ← mul_assoc, invOf_mul_self, one_mul]

/-- `x ∘ (buildThreeH s0 0 0 u v 0)`, i.e. `x` times a general row/column-`0`-supported piece
(diagonal `s0` plus off-diagonal `u`, `v` at `(0,1)`, `(0,2)`) -- the lemma `jordan_case_diag0`
actually needs, since both `x ∘ y` and `(x ∘ x) ∘ y` (for `y = diagPiece0 r`) are already of this
shape by `buildThreeH_mul_diagPiece0`. The `(1,1)`/`(2,2)` diagonal entries are stated via
`innerProduct (star p) (star u)`/`innerProduct (star q) (star v)` rather than the simplified
`innerProduct p u`/`innerProduct q v` (equal by `innerProduct_star_star`, but not what the raw
computation directly produces) so `scalarEmbed_innerProduct_eq` alone can close every diagonal
entry uniformly. The `(1,2)`/`(2,1)` entries (`⅟2 • (star p * v + star u * q)`) are the one place
two genuinely independent octonion products survive unresolved, carried through as-is. -/
private lemma buildThreeH_mul_shape001 (r0 r1 r2 s0 : R) (p q t u v : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * buildThreeH s0 0 0 u v 0 =
      buildThreeH
        (r0 * s0 + innerProduct p u + innerProduct q v)
        (innerProduct (star p) (star u))
        (innerProduct (star q) (star v))
        ((⅟2 : R) • ((r0 + r1) • u + s0 • p + v * star t))
        ((⅟2 : R) • ((r0 + r2) • v + s0 • q + u * t))
        ((⅟2 : R) • (star p * v + star u * q)) := by
  have hmul : (buildThreeH r0 r1 r2 p q t * buildThreeH s0 0 0 u v 0).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree s0 0 0 u v 0 +
        buildThree s0 0 0 u v 0 * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;>
    simp [-mul_fst, -mul_snd, -innerProduct_apply]
  · have key : (⅟2 : R) • (scalarEmbed (r0 * s0) : Octonion R a b c) +
        (⅟2 : R) • (scalarEmbed (r0 * s0) : Octonion R a b c) = scalarEmbed (r0 * s0) := by
      rw [← two_smul R, smul_smul, mul_comm, invOf_mul_self, one_smul]
    rw [scalarEmbed_innerProduct_eq, scalarEmbed_innerProduct_eq, ← map_mul, ← map_mul,
      show s0 * r0 = r0 * s0 from mul_comm s0 r0]
    linear_combination (norm := module) key
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [scalarEmbed_innerProduct_eq, star_star]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · module
  · simp only [scalarEmbed_innerProduct_eq, star_star]; module

/-- The `diagPiece1` analogue of `buildThreeH_mul_shape001`: `x * (buildThreeH 0 s1 0 u 0 w)`, i.e.
`x` times a general row/column-`1`-supported piece (diagonal `s1` plus off-diagonal `u`, `w` at
`(0,1)`, `(1,2)`). Derived the same way, by direct `Matrix.mul_apply` expansion of the (now
differently-supported) second factor. -/
private lemma buildThreeH_mul_shape010 (r0 r1 r2 s1 : R) (p q t u w : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * buildThreeH 0 s1 0 u 0 w =
      buildThreeH
        (innerProduct p u)
        (r1 * s1 + innerProduct (star p) (star u) + innerProduct t w)
        (innerProduct (star t) (star w))
        ((⅟2 : R) • ((r0 + r1) • u + s1 • p + q * star w))
        ((⅟2 : R) • (p * w + u * t))
        ((⅟2 : R) • ((r1 + r2) • w + s1 • t + star u * q)) := by
  have hmul : (buildThreeH r0 r1 r2 p q t * buildThreeH 0 s1 0 u 0 w).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree 0 s1 0 u 0 w +
        buildThree 0 s1 0 u 0 w * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;>
    simp [-mul_fst, -mul_snd, -innerProduct_apply]
  · simp only [scalarEmbed_innerProduct_eq]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · have key : (⅟2 : R) • (scalarEmbed (r1 * s1) : Octonion R a b c) +
        (⅟2 : R) • (scalarEmbed (r1 * s1) : Octonion R a b c) = scalarEmbed (r1 * s1) := by
      rw [← two_smul R, smul_smul, mul_comm, invOf_mul_self, one_smul]
    simp only [mul_both_scalarEmbed, show s1 * r1 = r1 * s1 from mul_comm s1 r1,
      scalarEmbed_innerProduct_eq, star_star]
    linear_combination (norm := module) key
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [scalarEmbed_innerProduct_eq, star_star]; module

/-- The `diagPiece2` analogue of `buildThreeH_mul_shape001`/`buildThreeH_mul_shape010`: `x *
(buildThreeH 0 0 s2 0 v w)`, i.e. `x` times a general row/column-`2`-supported piece (diagonal `s2`
plus off-diagonal `v`, `w` at `(0,2)`, `(1,2)`). -/
private lemma buildThreeH_mul_shape100 (r0 r1 r2 s2 : R) (p q t v w : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * buildThreeH 0 0 s2 0 v w =
      buildThreeH
        (innerProduct q v)
        (innerProduct t w)
        (r2 * s2 + innerProduct (star q) (star v) + innerProduct (star t) (star w))
        ((⅟2 : R) • (q * star w + v * star t))
        ((⅟2 : R) • ((r0 + r2) • v + p * w + s2 • q))
        ((⅟2 : R) • ((r1 + r2) • w + s2 • t + star p * v)) := by
  have hmul : (buildThreeH r0 r1 r2 p q t * buildThreeH 0 0 s2 0 v w).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree 0 0 s2 0 v w +
        buildThree 0 0 s2 0 v w * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;>
    simp [-mul_fst, -mul_snd, -innerProduct_apply]
  · simp only [scalarEmbed_innerProduct_eq]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · module
  · simp only [scalarEmbed_innerProduct_eq]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · have key : (⅟2 : R) • (scalarEmbed (r2 * s2) : Octonion R a b c) +
        (⅟2 : R) • (scalarEmbed (r2 * s2) : Octonion R a b c) = scalarEmbed (r2 * s2) := by
      rw [← two_smul R, smul_smul, mul_comm, invOf_mul_self, one_smul]
    simp only [mul_both_scalarEmbed, show s2 * r2 = r2 * s2 from mul_comm s2 r2,
      scalarEmbed_innerProduct_eq, star_star]
    linear_combination (norm := module) key

/-- The fully general product `buildThreeH r0 r1 r2 p q t * buildThreeH s0 s1 s2 u v w`, with both
factors' diagonal and off-diagonal entries unrestricted. `buildThreeH_mul_self`
(`s0=r0,...,u=p,...`) and `buildThreeH_mul_shape001/010/100` (setting two of `s0,s1,s2` and one of
`u,v,w` to `0`) are special cases, but this general form is what's needed for the off-diagonal
Jordan-identity cases (`jordan_case_off01/02/12`), since e.g. `x * (offPiece01 o)` is itself a
*generic* `buildThreeH`, not one of the restricted shapes. -/
private lemma buildThreeH_mul_general (r0 r1 r2 s0 s1 s2 : R) (p q t u v w : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * buildThreeH s0 s1 s2 u v w =
      buildThreeH
        (r0 * s0 + innerProduct p u + innerProduct q v)
        (r1 * s1 + innerProduct (star p) (star u) + innerProduct t w)
        (r2 * s2 + innerProduct (star q) (star v) + innerProduct (star t) (star w))
        ((⅟2 : R) • ((r0 + r1) • u + (s0 + s1) • p + q * star w + v * star t))
        ((⅟2 : R) • ((r0 + r2) • v + (s0 + s2) • q + p * w + u * t))
        ((⅟2 : R) • (star p * v + star u * q + (r1 + r2) • w + (s1 + s2) • t)) := by
  have hmul : (buildThreeH r0 r1 r2 p q t * buildThreeH s0 s1 s2 u v w).val =
      (⅟2 : R) • (buildThree r0 r1 r2 p q t * buildThree s0 s1 s2 u v w +
        buildThree s0 s1 s2 u v w * buildThree r0 r1 r2 p q t) := rfl
  apply Subtype.ext
  rw [hmul]
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [buildThreeH, buildThree] <;>
    simp [-mul_fst, -mul_snd, -innerProduct_apply]
  · have key : (⅟2 : R) • (scalarEmbed (r0 * s0) : Octonion R a b c) +
        (⅟2 : R) • (scalarEmbed (r0 * s0) : Octonion R a b c) = scalarEmbed (r0 * s0) := by
      rw [← two_smul R, smul_smul, mul_comm, invOf_mul_self, one_smul]
    simp only [mul_both_scalarEmbed, show s0 * r0 = r0 * s0 from mul_comm s0 r0,
      scalarEmbed_innerProduct_eq]
    linear_combination (norm := module) key
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · have key : (⅟2 : R) • (scalarEmbed (r1 * s1) : Octonion R a b c) +
        (⅟2 : R) • (scalarEmbed (r1 * s1) : Octonion R a b c) = scalarEmbed (r1 * s1) := by
      rw [← two_smul R, smul_smul, mul_comm, invOf_mul_self, one_smul]
    simp only [mul_both_scalarEmbed, show s1 * r1 = r1 * s1 from mul_comm s1 r1,
      scalarEmbed_innerProduct_eq, star_star]
    linear_combination (norm := module) key
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · simp only [mul_scalarEmbed, scalarEmbed_mul]; module
  · have key : (⅟2 : R) • (scalarEmbed (r2 * s2) : Octonion R a b c) +
        (⅟2 : R) • (scalarEmbed (r2 * s2) : Octonion R a b c) = scalarEmbed (r2 * s2) := by
      rw [← two_smul R, smul_smul, mul_comm, invOf_mul_self, one_smul]
    simp only [mul_both_scalarEmbed, show s2 * r2 = r2 * s2 from mul_comm s2 r2,
      scalarEmbed_innerProduct_eq, star_star]
    linear_combination (norm := module) key

/-- `x * (offPiece01 o)`: the `s0 = 0, v = 0` specialization of `buildThreeH_mul_shape001` (since
`offPiece01 o` is literally `buildThreeH 0 0 0 o 0 0`), with the resulting zero terms simplified
away. -/
private lemma buildThreeH_mul_offPiece01 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * offPiece01 o =
      buildThreeH (innerProduct p o) (innerProduct (star p) (star o)) 0
        ((⅟2 : R) • ((r0 + r1) • o)) ((⅟2 : R) • (o * t)) ((⅟2 : R) • (star o * q)) := by
  simp only [offPiece01, buildThreeH_mul_shape001, mul_zero, map_zero, add_zero, zero_add,
    zero_smul, smul_zero, star_zero, zero_mul]

/-- `x * (offPiece02 o)`: the `s0 = 0, u = 0` specialization of `buildThreeH_mul_shape001` (since
`offPiece02 o` is literally `buildThreeH 0 0 0 0 o 0`). -/
private lemma buildThreeH_mul_offPiece02 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * offPiece02 o =
      buildThreeH (innerProduct q o) 0 (innerProduct (star q) (star o))
        ((⅟2 : R) • (o * star t)) ((⅟2 : R) • ((r0 + r2) • o)) ((⅟2 : R) • (star p * o)) := by
  simp only [offPiece02, buildThreeH_mul_shape001, mul_zero, map_zero, add_zero, zero_smul,
    smul_zero, star_zero, zero_mul, zero_add]

/-- `x * (offPiece12 o)`: the `s1 = 0, u = 0` specialization of `buildThreeH_mul_shape010` (since
`offPiece12 o` is literally `buildThreeH 0 0 0 0 0 o`). -/
private lemma buildThreeH_mul_offPiece12 (r0 r1 r2 : R) (p q t o : Octonion R a b c) :
    buildThreeH r0 r1 r2 p q t * offPiece12 o =
      buildThreeH 0 (innerProduct t o) (innerProduct (star t) (star o))
        ((⅟2 : R) • (q * star o)) ((⅟2 : R) • (p * o)) ((⅟2 : R) • ((r1 + r2) • o)) := by
  simp only [offPiece12, buildThreeH_mul_shape010, mul_zero, map_zero, add_zero, zero_smul,
    smul_zero, star_zero, zero_mul, zero_add]

section NuclearHyps

variable (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0)
  (hc : ∀ x : R, c * x = 0 → x = 0)

include ha hb hc in
set_option maxHeartbeats 1000000 in
/-- `AlbertAlgebra` is a Jordan algebra whenever `a`, `b`, `c` are non-zero-divisors: that
regularity is exactly what `Octonion.nuclearInvolution` needs to show `Octonion R a b c` is a
nuclear involution, the hypothesis `hermitian_jordan_identity` needs for `jordan_identity` below.
Not tagged `instance` since it takes explicit hypotheses beyond the ambient typeclasses -- see
`JORDAN_IDENTITY_PLAN.md`. -/
@[reducible] def ofAlbert : JordanAlgebra R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) where
  jordan_mul_comm := by
    intro x y
    apply Subtype.ext
    change (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) =
      (⅟2 : R) • (y.1 * x.1 + x.1 * y.1)
    rw [add_comm]
  jordan_identity x y := by
    apply Subtype.ext
    have hsq : (x * x).val = x.1 * x.1 := by
      show (⅟2 : R) • (x.1 * x.1 + x.1 * x.1) = _
      rw [← two_smul R, smul_smul, invOf_mul_self, one_smul]
    have hxy : (x * y).val = (⅟2 : R) • (x.1 * y.1 + y.1 * x.1) := rfl
    have hxxy : (x * x * y).val = (⅟2 : R) • (x.1 * x.1 * y.1 + y.1 * (x.1 * x.1)) := by
      show (⅟2 : R) • ((x * x).val * y.1 + y.1 * (x * x).val) = _
      rw [hsq]
    have hLHS : (x * x * (x * y)).val =
        ((⅟2 : R) * (⅟2 : R)) •
          ((x.1 * x.1) * (x.1 * y.1 + y.1 * x.1) + (x.1 * y.1 + y.1 * x.1) * (x.1 * x.1)) := by
      show (⅟2 : R) • ((x * x).val * (x * y).val + (x * y).val * (x * x).val) = _
      rw [hsq, hxy, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul]
    have hRHS : (x * (x * x * y)).val =
        ((⅟2 : R) * (⅟2 : R)) •
          (x.1 * (x.1 * x.1 * y.1 + y.1 * (x.1 * x.1)) +
            (x.1 * x.1 * y.1 + y.1 * (x.1 * x.1)) * x.1) := by
      show (⅟2 : R) • (x.1 * (x * x * y).val + (x * x * y).val * x.1) = _
      rw [hxxy, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul]
    rw [hLHS, hRHS]
    congr 1
    haveI := Octonion.nuclearInvolution ha hb hc
    have key := hermitian_jordan_identity x.1 y.1 x.2 y.2
    linear_combination (norm := abel_nf) key

end NuclearHyps

/-! ### Formal reality

Over an ordered `R`, with each Cayley-Dickson step's structure constant negative for the two
quaternion-level doublings (`a < 0`, `b < 0`, generalizing Hamilton's quaternions), the octonion
norm form `N(x) = N(x.1) + c * N(x.2)` (`Octonion.mul_star_self_eq_scalarEmbed`) is
positive-definite exactly when `0 < c` -- the usual octonions being `a = b = -1`, `c = 1`. (`c < 0`
would let `N` go arbitrarily negative by scaling `x.2`, since `N(x.2) ≥ 0` already from `a < 0`,
`b < 0` alone.) `trace(A * A)` for a Hermitian `A` then decomposes into a sum of those norms over
the entries -- exactly as in `ComplexQM.isFormallyReal`/`QuaternionicQM.isFormallyReal`, now via
`buildThreeH_mul_self` in place of `Matrix.trace`/`MooreDeterminant`. -/

section FormallyReal

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
/-- The real part of a quaternion's norm `star q * q`, expanded in coordinates -- a pure ring
identity, no positivity needed. The `ℍ[R, a, 0, b]` analogue of `QuaternionicQM.mul_star_re_eq`. -/
private theorem quat_star_mul_re_eq (q : ℍ[R, a, 0, b]) :
    (star q * q).re =
      q.re * q.re - a * q.imI * q.imI - b * q.imJ * q.imJ + a * b * q.imK * q.imK := by
  show (star q).re * q.re + a * (star q).imI * q.imI + b * (star q).imJ * q.imJ +
      (0 : R) * b * (star q).imJ * q.imK - a * b * (star q).imK * q.imK = _
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
private theorem quat_norm_nonneg (ha : a < 0) (hb : b < 0) (q : ℍ[R, a, 0, b]) :
    0 ≤ (star q * q).re := by
  rw [quat_star_mul_re_eq]
  have h1 : 0 ≤ q.re * q.re := mul_self_nonneg _
  have h2 : 0 ≤ -a * (q.imI * q.imI) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h3 : 0 ≤ -b * (q.imJ * q.imJ) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h4 : 0 ≤ a * b * (q.imK * q.imK) :=
    mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (mul_self_nonneg _)
  nlinarith

omit [Invertible (2 : R)] in
set_option linter.unusedSectionVars false in
private theorem quat_norm_eq_zero_iff (ha : a < 0) (hb : b < 0) (q : ℍ[R, a, 0, b]) :
    (star q * q).re = 0 ↔ q = 0 := by
  refine ⟨fun hq => ?_, fun hq => by simp [hq]⟩
  rw [quat_star_mul_re_eq] at hq
  have h1 : 0 ≤ q.re * q.re := mul_self_nonneg _
  have h2 : 0 ≤ -a * (q.imI * q.imI) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h3 : 0 ≤ -b * (q.imJ * q.imJ) := mul_nonneg (by linarith) (mul_self_nonneg _)
  have h4 : 0 ≤ a * b * (q.imK * q.imK) :=
    mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (mul_self_nonneg _)
  have hre : q.re * q.re = 0 := by nlinarith
  have hI : -a * (q.imI * q.imI) = 0 := by nlinarith
  have hJ : -b * (q.imJ * q.imJ) = 0 := by nlinarith
  have hK : a * b * (q.imK * q.imK) = 0 := by nlinarith
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

omit [Invertible (2 : R)] in
/-- The octonion norm form is positive-definite: `a < 0`, `b < 0` give `quat_norm_nonneg` on each
quaternion component, and `0 < c` keeps the `c *` term from flipping the second component's
contribution negative. -/
private theorem octonionNorm_nonneg (ha : a < 0) (hb : b < 0) (hc : 0 < c)
    (x : Octonion R a b c) : 0 ≤ (star x.1 * x.1).re + c * (star x.2 * x.2).re :=
  add_nonneg (quat_norm_nonneg ha hb x.1) (mul_nonneg hc.le (quat_norm_nonneg ha hb x.2))

omit [Invertible (2 : R)] in
private theorem octonionNorm_eq_zero_iff (ha : a < 0) (hb : b < 0) (hc : 0 < c)
    (x : Octonion R a b c) : (star x.1 * x.1).re + c * (star x.2 * x.2).re = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have h1 : 0 ≤ (star x.1 * x.1).re := quat_norm_nonneg ha hb x.1
  have h2 : 0 ≤ c * (star x.2 * x.2).re := mul_nonneg hc.le (quat_norm_nonneg ha hb x.2)
  have he1 : (star x.1 * x.1).re = 0 := by linarith
  have he2 : c * (star x.2 * x.2).re = 0 := by linarith
  have he2' : (star x.2 * x.2).re = 0 := by
    rcases mul_eq_zero.mp he2 with h | h
    · exact absurd h (by linarith)
    · exact h
  exact Octonion.ext ((quat_norm_eq_zero_iff ha hb x.1).mp he1)
    ((quat_norm_eq_zero_iff ha hb x.2).mp he2')

omit [Invertible (2 : R)] in
/-- `x * star x = 0 ↔ x = 0`, the octonion-level positivity fact `IsFormallyReal` on
`AlbertAlgebra` ultimately needs. -/
private theorem mul_star_self_eq_zero_iff (ha : a < 0) (hb : b < 0) (hc : 0 < c)
    (x : Octonion R a b c) : x * star x = 0 ↔ x = 0 := by
  rw [mul_star_self_eq_scalarEmbed]
  refine ⟨fun h => (octonionNorm_eq_zero_iff ha hb hc x).mp ?_, fun h => by simp [h]⟩
  exact scalarEmbed_injective (h.trans (map_zero scalarEmbed).symm)

/-- The generic trace: the sum of the three (real) diagonal coordinates, the `AlbertAlgebra`
analogue of the ordinary matrix trace (off-diagonal entries don't contribute since they're not on
the diagonal). -/
def trace (x : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) : R :=
  HermitianOctonionMatrixThree.diagCoord x 0 + HermitianOctonionMatrixThree.diagCoord x 1 +
    HermitianOctonionMatrixThree.diagCoord x 2

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `trace (x * x)` decomposes into a sum of six norm terms, two per diagonal slot -- directly
from `buildThreeH_mul_self`'s three diagonal-coordinate formulas, each a sum of a perfect square
(`r_i * r_i`) and two octonion norms of `x`'s own off-diagonal entries. -/
private theorem trace_mul_self_eq (r0 r1 r2 : R) (p q t : Octonion R a b c) :
    trace (buildThreeH r0 r1 r2 p q t * buildThreeH r0 r1 r2 p q t) =
      r0 * r0 + (star p.1 * p.1).re + c * (star p.2 * p.2).re +
        ((star q.1 * q.1).re + c * (star q.2 * q.2).re) +
        (r1 * r1 + ((star p.1 * p.1).re + c * (star p.2 * p.2).re) +
          ((star t.1 * t.1).re + c * (star t.2 * t.2).re)) +
        (r2 * r2 + ((star q.1 * q.1).re + c * (star q.2 * q.2).re) +
          ((star t.1 * t.1).re + c * (star t.2 * t.2).re)) := by
  simp only [trace, buildThreeH_mul_self, HermitianOctonionMatrixThree.diagCoord_buildThreeH_0,
    HermitianOctonionMatrixThree.diagCoord_buildThreeH_1,
    HermitianOctonionMatrixThree.diagCoord_buildThreeH_2]
  rw [show (p * star p).1.re = (star p.1 * p.1).re + c * (star p.2 * p.2).re from
      diag_just_11 _ _ (mul_star_self_eq_scalarEmbed p),
    show (q * star q).1.re = (star q.1 * q.1).re + c * (star q.2 * q.2).re from
      diag_just_11 _ _ (mul_star_self_eq_scalarEmbed q),
    show (star p * p).1.re = (star p.1 * p.1).re + c * (star p.2 * p.2).re from
      diag_just_11 _ _ (star_mul_self_eq_scalarEmbed p),
    show (star q * q).1.re = (star q.1 * q.1).re + c * (star q.2 * q.2).re from
      diag_just_11 _ _ (star_mul_self_eq_scalarEmbed q),
    show (t * star t).1.re = (star t.1 * t.1).re + c * (star t.2 * t.2).re from
      diag_just_11 _ _ (mul_star_self_eq_scalarEmbed t),
    show (star t * t).1.re = (star t.1 * t.1).re + c * (star t.2 * t.2).re from
      diag_just_11 _ _ (star_mul_self_eq_scalarEmbed t)]
  ring

omit i2 [LinearOrder R] [IsStrictOrderedRing R] in
private theorem trace_add (x y : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    trace (x + y) = trace x + trace y := by
  simp only [trace, HermitianOctonionMatrixThree.diagCoord]
  show ((x + y).val 0 0).1.re + ((x + y).val 1 1).1.re + ((x + y).val 2 2).1.re = _
  simp [Matrix.add_apply]
  ring

omit i2 [LinearOrder R] [IsStrictOrderedRing R] in
private theorem trace_zero : trace (0 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) = 0 := by
  simp [trace, HermitianOctonionMatrixThree.diagCoord]

/-- The `trace` map bundled as an `AddMonoidHom`, purely so `map_sum` is available for the
`Finset.sum` manipulation in `isFormallyReal`. -/
private def traceHom : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) →+ R where
  toFun := trace
  map_zero' := trace_zero
  map_add' := trace_add

omit i2 [LinearOrder R] [IsStrictOrderedRing R] in
private theorem buildThreeH_zero :
    buildThreeH (0 : R) 0 0 (0 : Octonion R a b c) 0 0 = 0 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [buildThreeH, buildThree]

variable (hna : ∀ x : R, a * x = 0 → x = 0) (hnb : ∀ x : R, b * x = 0 → x = 0)
  (hnc : ∀ x : R, c * x = 0 → x = 0)

include hna hnb hnc in
theorem isFormallyReal (ha : a < 0) (hb : b < 0) (hc : 0 < c) :
    @IsFormallyReal R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) _ (ofAlbert hna hnb hnc) := by
  letI := ofAlbert hna hnb hnc
  refine ⟨fun {ι} _ X hX i => ?_⟩
  have hex : ∀ k, ∃ r0 r1 r2 p q t, X k = buildThreeH r0 r1 r2 p q t :=
    fun k => ⟨_, _, _, _, _, _, HermitianOctonionMatrixThree.eq_buildThreeH (X k)⟩
  choose r0 r1 r2 p q t hXeq using hex
  have hsum : ∑ k, trace (X k * X k) = 0 := by
    have h : traceHom (∑ k, X k * X k) = ∑ k, traceHom (X k * X k) := map_sum traceHom _ _
    have hX' : (∑ k, X k * X k) = 0 := hX
    rw [hX', map_zero] at h
    exact h.symm
  have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ trace (X k * X k) := by
    intro k _
    rw [hXeq k, trace_mul_self_eq]
    have h1 := octonionNorm_nonneg ha hb hc (p k)
    have h2 := octonionNorm_nonneg ha hb hc (q k)
    have h3 := octonionNorm_nonneg ha hb hc (t k)
    nlinarith [mul_self_nonneg (r0 k), mul_self_nonneg (r1 k), mul_self_nonneg (r2 k)]
  have hzero : trace (X i * X i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  rw [hXeq i, trace_mul_self_eq] at hzero
  have hNp := octonionNorm_nonneg ha hb hc (p i)
  have hNq := octonionNorm_nonneg ha hb hc (q i)
  have hNt := octonionNorm_nonneg ha hb hc (t i)
  have hr0 : r0 i * r0 i = 0 := by nlinarith
  have hr1 : r1 i * r1 i = 0 := by nlinarith
  have hr2 : r2 i * r2 i = 0 := by nlinarith
  have hNp0 : (star (p i).1 * (p i).1).re + c * (star (p i).2 * (p i).2).re = 0 := by nlinarith
  have hNq0 : (star (q i).1 * (q i).1).re + c * (star (q i).2 * (q i).2).re = 0 := by nlinarith
  have hNt0 : (star (t i).1 * (t i).1).re + c * (star (t i).2 * (t i).2).re = 0 := by nlinarith
  rw [hXeq i, mul_self_eq_zero.mp hr0, mul_self_eq_zero.mp hr1, mul_self_eq_zero.mp hr2,
    (octonionNorm_eq_zero_iff ha hb hc (p i)).mp hNp0,
    (octonionNorm_eq_zero_iff ha hb hc (q i)).mp hNq0,
    (octonionNorm_eq_zero_iff ha hb hc (t i)).mp hNt0, buildThreeH_zero]

omit i2 [LinearOrder R] [IsStrictOrderedRing R] in
private theorem trace_smul (r : R) (x : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    trace (r • x) = r * trace x := by
  simp only [trace, HermitianOctonionMatrixThree.diagCoord]
  show ((r • x).val 0 0).1.re + ((r • x).val 1 1).1.re + ((r • x).val 2 2).1.re = _
  simp [Matrix.smul_apply]
  ring

/-- `trace` bundled as an `R`-linear map, the form `IsFormallyRealDetTrace.trace` needs. -/
private def traceₗ : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c) →ₗ[R] R where
  toFun := trace
  map_add' := trace_add
  map_smul' r x := by simpa using trace_smul r x

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem trace_one : trace (1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) = 3 := by
  show ((1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)).val 0 0).1.re +
      ((1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)).val 1 1).1.re +
      ((1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)).val 2 2).1.re = 3
  rw [show (1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)).val = 1 from rfl]
  simp [Matrix.one_apply_eq]
  ring_nf

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem buildThreeH_smul (r r0 r1 r2 : R) (p q t : Octonion R a b c) :
    r • buildThreeH r0 r1 r2 p q t =
      buildThreeH (r * r0) (r * r1) (r * r2) (r • p) (r • q) (r • t) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [buildThreeH, buildThree, smul_scalarEmbed]

/-- The `Freudenthal`/Jordan cubic-form determinant of a `3 x 3` Hermitian octonionic matrix, the
`3 x 3` analogue of the classical Hermitian-matrix determinant expansion `det = ξ1ξ2ξ3 - ξ1|x|² -
ξ2|y|² - ξ3|z|² + 2 Re(x y z)` (diagonal entries `ξ1,ξ2,ξ3`, off-diagonal entries `x = (1,2)`, `y =
(0,2)`, `z = (0,1)`). Just the formula: none of the genuine multiplicative/cubic-form identities
(needing Artin's theorem/the Freudenthal machinery in full) are proved about it here, only what
`IsFormallyRealDetTrace` itself asks for (`det_smul`, `det_one`, via `det_buildThreeH` below). -/
def det (x : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) : R :=
  HermitianOctonionMatrixThree.diagCoord x 0 * HermitianOctonionMatrixThree.diagCoord x 1 *
      HermitianOctonionMatrixThree.diagCoord x 2
    - HermitianOctonionMatrixThree.diagCoord x 0 *
        ((star (x.val 1 2).1 * (x.val 1 2).1).re + c * (star (x.val 1 2).2 * (x.val 1 2).2).re)
    - HermitianOctonionMatrixThree.diagCoord x 1 *
        ((star (x.val 0 2).1 * (x.val 0 2).1).re + c * (star (x.val 0 2).2 * (x.val 0 2).2).re)
    - HermitianOctonionMatrixThree.diagCoord x 2 *
        ((star (x.val 0 1).1 * (x.val 0 1).1).re + c * (star (x.val 0 1).2 * (x.val 0 1).2).re)
    + 2 * (x.val 1 2 * (x.val 0 2 * star (x.val 0 1))).1.re

omit i2 [LinearOrder R] [IsStrictOrderedRing R] in
private theorem det_buildThreeH (r0 r1 r2 : R) (p q t : Octonion R a b c) :
    det (buildThreeH r0 r1 r2 p q t) =
      r0 * r1 * r2
        - r0 * ((star t.1 * t.1).re + c * (star t.2 * t.2).re)
        - r1 * ((star q.1 * q.1).re + c * (star q.2 * q.2).re)
        - r2 * ((star p.1 * p.1).re + c * (star p.2 * p.2).re)
        + 2 * (t * (q * star p)).1.re := by
  simp [det, buildThreeH, buildThree, HermitianOctonionMatrixThree.diagCoord]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem det_smul (r : R) (x : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) :
    det (r • x) = r ^ 3 • det x := by
  obtain ⟨r0, r1, r2, p, q, t, rfl⟩ : ∃ r0 r1 r2 p q t, x = buildThreeH r0 r1 r2 p q t :=
    ⟨_, _, _, _, _, _, HermitianOctonionMatrixThree.eq_buildThreeH x⟩
  rw [buildThreeH_smul, det_buildThreeH, det_buildThreeH, smul_eq_mul]
  simp only [smul_fst, smul_snd, QuaternionAlgebra.star_smul', mul_smul_comm, smul_mul_assoc]
  simp
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem AlbertAlgebra_one_val :
    (1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)).val = 1 := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem det_one : det (1 : AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) = 1 := by
  simp [det, HermitianOctonionMatrixThree.diagCoord, AlbertAlgebra_one_val]

include hna hnb hnc in
/-- Rank `3`, matching the classical Albert algebra: both the trace half (`traceₗ`/`trace_one`,
from `buildThreeH_mul_self`/`Octonion.mul_star_self_eq_scalarEmbed`, exactly as `isFormallyReal`
was) and the determinant half (`det`/`det_smul`/`det_one`, the Freudenthal cubic-form formula
above) are filled in. What isn't proved is that `det` satisfies any further multiplicative or
cubic-form identity beyond the two `IsFormallyRealDetTrace` fields ask for -- those would need
Artin's theorem/the full Freudenthal machinery, not attempted here. -/
noncomputable def detTrace (ha : a < 0) (hb : b < 0) (hc : 0 < c) :
    @IsFormallyRealDetTrace R (AlbertAlgebra (R:=R) (a:=a) (b:=b) (c:=c)) _ (ofAlbert hna hnb hnc)
      (isFormallyReal hna hnb hnc ha hb hc) := by
  letI := ofAlbert hna hnb hnc
  letI := isFormallyReal hna hnb hnc ha hb hc
  exact
    { rank := 3
      trace := traceₗ
      det := det
      det_smul := det_smul
      trace_one := trace_one
      det_one := det_one }

end FormallyReal

end ThreeByThree

end Octonion
