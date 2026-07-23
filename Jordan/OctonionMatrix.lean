import Mathlib.LinearAlgebra.Matrix.Unique
import Jordan.RealQM
import Jordan.SpinFactor
import Jordan.Octonion

/-!
# Hermitian octonionic matrices

The Hermitian `n × n` matrices over `Octonion R a b c`, with the symmetrized product `⅟2 • (AB +
BA)`, plus the `1 x 1` and `2 x 2` cases: the `1 x 1` case collapses to plain `R` (matching
`RealQM`'s `1 x 1` Jordan algebra), and the `2 x 2` case is the spin-factor construction, matching
`SpinFactor`. The genuinely exceptional `3 x 3` (Albert algebra) case lives in
`Jordan.AlbertAlgebra`, since octonion non-associativity makes it a substantially different, much
harder argument than these two.
-/

section OctonionMatrices

variable {R : Type*}
  [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
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

instance : IsScalarTower R (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
    (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) := inferInstance

instance : SMulCommClass R (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
    (OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) := inferInstance

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

omit [Fintype n] [DecidableEq n] in
lemma diag_real
  (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
  (i : n) :
    ∃ r : R, M.val i i = Octonion.scalarEmbed r := by
  have h := congrArg (fun M => M i i) M.property
  exact (Octonion.isSelfAdjoint_iff (M.val i i)).mp h

omit i2 in
set_option linter.unusedSectionVars false in
lemma diag_just_11 (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.re = r := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_1i (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imI = 0 := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_1j (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imJ = 0 := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_1k (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.1.imK = 0 := by
  intro h
  simp [h]
omit i2 in
set_option linter.unusedSectionVars false in
private lemma diag_no_2 (x : Octonion R a b c) (r : R) : x = Octonion.scalarEmbed r -> x.2 = 0 := by
  intro h
  simp [h]

omit i2 [StarRing R] [TrivialStar R] in
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

instance CommRing_HermitianOctonionMatrix : NonAssocCommRing (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
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

/-- `R`-scaling associates with the symmetrized Hermitian product `⅟2 • (AB + BA)`. Not inherited
automatically from `IsScalarTower R (OctonionMatrix ...) (OctonionMatrix ...)`, since `Mul` on
`HermitianOctonionMatrix` is the symmetrized product, not the ambient matrix product. -/
instance IsScalarTower_HermitianOctonionMatrix :
    IsScalarTower R (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
      (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  smul_assoc r x y := by
    apply Subtype.ext
    change (⅟2 : R) • ((r • x.1) * y.1 + y.1 * (r • x.1)) =
      r • ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1))
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_comm (⅟2 : R) r]

/-- `R`-scaling commutes across the symmetrized Hermitian product, for the same reason
`IsScalarTower_HermitianOctonionMatrix` needs its own proof. -/
instance SMulCommClass_HermitianOctonionMatrix :
    SMulCommClass R (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n))
      (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  smul_comm r x y := by
    apply Subtype.ext
    change r • ((⅟2 : R) • (x.1 * y.1 + y.1 * x.1)) =
      (⅟2 : R) • (x.1 * (r • y.1) + (r • y.1) * x.1)
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_comm r (⅟2 : R)]

instance Star_HermitianOctonionMatrix : Star (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star x := x

instance TrivialStar_HermitianOctonionMatrix : TrivialStar (HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=n)) where
  star_trivial := by
    intro r
    rfl

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
variable {a b c : R}

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

omit i2 in
private lemma HermitianOctonionMatrixOne.add_re
    (M N : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 1)) :
    (((M + N).val 0 0).1.re : R) = (M.val 0 0).1.re + (N.val 0 0).1.re := by
  rfl

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

The `2 x 2` construction is the spin-factor case, via the usual trace/trace-free split: writing a
Hermitian matrix as `![![r, x], [star x, s]]` with `r s : R` and `x : Octonion R a b c`, the
*scalar* coordinate is the half-trace `t = (r + s) / 2`, and the *vector* coordinate is the
trace-free part `(x, (r - s) / 2) : Octonion R a b c × R` -- **not** simply the two diagonal
entries directly, since only their half-sum survives as the scalar while their half-difference
joins `x` in the vector part. The intended comparison theorem here is an explicit `≃+*`, parallel
to `ofSymmetricMatricesOne`, but landing on `SpinFactor R (Octonion R a b c × R) B` for the
appropriate bilinear form `B`, instead of the `1 x 1` scalar algebra. -/
section TwoByTwo

variable {R : Type*}
variable [CommRing R] [i2: Invertible (2 : R)] [StarRing R] [TrivialStar R]
variable {a b c : R}

omit i2 in
/-- The off-diagonal Hermitian-symmetry condition, the `2 x 2` analogue of `diag_real` for the
diagonal: in a Hermitian `2 x 2` octonionic matrix, the `(1,0)` entry is forced to be the
conjugate of the `(0,1)` entry. -/
private lemma HermitianOctonionMatrixTwo.off_diag
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) :
    M.val 1 0 = star (M.val 0 1) := by
  have h : star (M.val 1 0) = M.val 0 1 := congrFun (congrFun M.property 0) 1
  rw [← h, star_star]

/-- The half-trace of a Hermitian `2 x 2` octonionic matrix, `t = (r + s) / 2` where `r, s` are the
(real) diagonal entries -- read off directly via the quaternion real-part coordinate `.1.re`
(matching `diag_just_11`), so this needs no case split on `diag_real`. This is the scalar
coordinate of the intended `SpinFactor` identification; the division by `2` is genuinely needed
here (unlike `off_diag` above), since it must match `SpinFactor`'s fixed `a • y + b • x`
multiplication -- see the discussion above `TwoByTwo`. -/
private def HermitianOctonionMatrixTwo.traceHalf
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) : R :=
  ⅟(2 : R) * ((M.val 0 0).1.re + (M.val 1 1).1.re)

/-- The half-difference of the diagonal entries of a Hermitian `2 x 2` octonionic matrix,
`p = (r - s) / 2`. Together with the off-diagonal octonion `M.val 0 1`, this is the trace-free
"vector" coordinate of the intended `SpinFactor` identification. -/
private def HermitianOctonionMatrixTwo.diffHalf
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) : R :=
  ⅟(2 : R) * ((M.val 0 0).1.re - (M.val 1 1).1.re)

/-- The `(r, s) ↔ (t, p)` change of basis is invertible: given the two (real) diagonal entries
`r, s` produced by `diag_real`, the half-sum/half-difference `traceHalf`/`diffHalf` recover them
back via `r = t + p`, `s = t - p`. This is what makes the trace/trace-free decomposition a genuine
reparametrization of the diagonal data, not merely a one-way projection. -/
private lemma HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf
    (M : HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2)) :
    ∃ r s : R, M.val 0 0 = Octonion.scalarEmbed r ∧ M.val 1 1 = Octonion.scalarEmbed s ∧
      r = traceHalf M + diffHalf M ∧ s = traceHalf M - diffHalf M := by
  obtain ⟨r, hr⟩ := diag_real M 0
  obtain ⟨s, hs⟩ := diag_real M 1
  have hr' : (M.val 0 0).1.re = r := diag_just_11 (M.val 0 0) r hr
  have hs' : (M.val 1 1).1.re = s := diag_just_11 (M.val 1 1) s hs
  refine ⟨r, s, hr, hs, ?_, ?_⟩
  · unfold HermitianOctonionMatrixTwo.traceHalf HermitianOctonionMatrixTwo.diffHalf
    rw [hr', hs', ← mul_add]
    have : r + s + (r - s) = 2 * r := by ring
    rw [this, ← mul_assoc, invOf_mul_self, one_mul]
  · unfold HermitianOctonionMatrixTwo.traceHalf HermitianOctonionMatrixTwo.diffHalf
    rw [hr', hs', ← mul_sub]
    have : r + s - (r - s) = 2 * s := by ring
    rw [this, ← mul_assoc, invOf_mul_self, one_mul]

/-- The underlying function of `hermitianTwoBilin`: the octonion polarization form
`Octonion.innerProduct` on the octonion part, plus plain multiplication on the `R` part. Kept
separate so the bilinearity proofs below can be named lemmas, as with `innerProductFun` above. -/
private noncomputable def hermitianTwoBilinFun (z w : Octonion R a b c × R) : R :=
  Octonion.innerProduct z.1 w.1 + z.2 * w.2

private theorem hermitianTwoBilinFun_add_left (z₁ z₂ w : Octonion R a b c × R) :
    hermitianTwoBilinFun (z₁ + z₂) w = hermitianTwoBilinFun z₁ w + hermitianTwoBilinFun z₂ w := by
  unfold hermitianTwoBilinFun
  simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, add_mul]
  abel

private theorem hermitianTwoBilinFun_smul_left (r : R) (z w : Octonion R a b c × R) :
    hermitianTwoBilinFun (r • z) w = r * hermitianTwoBilinFun z w := by
  unfold hermitianTwoBilinFun
  simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_add,
    mul_assoc]

private theorem hermitianTwoBilinFun_add_right (z w₁ w₂ : Octonion R a b c × R) :
    hermitianTwoBilinFun z (w₁ + w₂) = hermitianTwoBilinFun z w₁ + hermitianTwoBilinFun z w₂ := by
  unfold hermitianTwoBilinFun
  simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]
  abel

private theorem hermitianTwoBilinFun_smul_right (r : R) (z w : Octonion R a b c × R) :
    hermitianTwoBilinFun z (r • w) = r * hermitianTwoBilinFun z w := by
  unfold hermitianTwoBilinFun
  simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, mul_add, mul_left_comm]

/-- The bilinear form on the trace-free vector space `Octonion R a b c × R`, making the `2 x 2`
Hermitian identification work. -/
private noncomputable def hermitianTwoBilin :
    LinearMap.BilinForm R (Octonion R a b c × R) :=
  LinearMap.mk₂ R hermitianTwoBilinFun
    hermitianTwoBilinFun_add_left hermitianTwoBilinFun_smul_left
    hermitianTwoBilinFun_add_right hermitianTwoBilinFun_smul_right

private def buildTwo (x : Octonion R a b c) (t p : R) :
    OctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2) :=
  !![Octonion.scalarEmbed (t + p), x; star x, Octonion.scalarEmbed (t - p)]

set_option linter.unusedSectionVars false in
private lemma buildTwo_isHermitian (x : Octonion R a b c) (t p : R) :
    star (buildTwo (R:=R) (a:=a) (b:=b) (c:=c) x t p) = buildTwo x t p := by
  apply Matrix.ext
  intro i j
  show star (buildTwo x t p j i) = buildTwo x t p i j
  fin_cases i <;> fin_cases j <;> simp [buildTwo, star_scalarEmbed, star_star]

private lemma traceHalf_buildTwo (x : Octonion R a b c) (t p : R) :
    HermitianOctonionMatrixTwo.traceHalf ⟨buildTwo x t p, buildTwo_isHermitian x t p⟩ = t := by
  show ⅟(2 : R) * ((buildTwo x t p 0 0).1.re + (buildTwo x t p 1 1).1.re) = t
  show ⅟(2 : R) * ((scalarEmbed (t + p) : Octonion R a b c).1.re +
    (scalarEmbed (t - p) : Octonion R a b c).1.re) = t
  rw [scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.algebraMap_eq]
  show ⅟(2 : R) * ((t + p) + (t - p)) = t
  rw [show (t + p) + (t - p) = 2 * t from by ring, ← mul_assoc, invOf_mul_self, one_mul]

private lemma diffHalf_buildTwo (x : Octonion R a b c) (t p : R) :
    HermitianOctonionMatrixTwo.diffHalf ⟨buildTwo x t p, buildTwo_isHermitian x t p⟩ = p := by
  show ⅟(2 : R) * ((buildTwo x t p 0 0).1.re - (buildTwo x t p 1 1).1.re) = p
  show ⅟(2 : R) * ((scalarEmbed (t + p) : Octonion R a b c).1.re -
    (scalarEmbed (t - p) : Octonion R a b c).1.re) = p
  rw [scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.algebraMap_eq]
  show ⅟(2 : R) * ((t + p) - (t - p)) = p
  rw [show (t + p) - (t - p) = 2 * p from by ring, ← mul_assoc, invOf_mul_self, one_mul]

/-- The intended explicit identification of `2 x 2` Hermitian octonionic matrices with the
appropriate `SpinFactor`, parallel to `ofSymmetricMatricesOne`: the scalar coordinate is
`traceHalf`, the vector coordinate is `(M.val 0 1, diffHalf M)`. -/
noncomputable def ofSymmetricMatricesTwo :
    HermitianOctonionMatrix (R:=R) (a:=a) (b:=b) (c:=c) (n:=Fin 2) ≃+*
      SpinFactor R (Octonion R a b c × R)
        (hermitianTwoBilin (R:=R) (a:=a) (b:=b) (c:=c)) where
  toFun M := SpinFactor.mk _ (M.val 0 1, HermitianOctonionMatrixTwo.diffHalf M)
    (HermitianOctonionMatrixTwo.traceHalf M)
  invFun z := ⟨buildTwo z.1.1 z.2 z.1.2, buildTwo_isHermitian z.1.1 z.2 z.1.2⟩
  left_inv M := by
    obtain ⟨r, s, hr, hs, hr', hs'⟩ := HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf M
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    show buildTwo (M.val 0 1) (HermitianOctonionMatrixTwo.traceHalf M)
        (HermitianOctonionMatrixTwo.diffHalf M) i j = M.val i j
    fin_cases i <;> fin_cases j
    · show scalarEmbed (HermitianOctonionMatrixTwo.traceHalf M + HermitianOctonionMatrixTwo.diffHalf M) =
        M.val 0 0
      rw [← hr', hr]
    · rfl
    · show star (M.val 0 1) = M.val 1 0
      exact (HermitianOctonionMatrixTwo.off_diag M).symm
    · show scalarEmbed (HermitianOctonionMatrixTwo.traceHalf M - HermitianOctonionMatrixTwo.diffHalf M) =
        M.val 1 1
      rw [← hs', hs]
  right_inv z := by
    apply SpinFactor.ext
    · show (buildTwo z.1.1 z.2 z.1.2 0 1, HermitianOctonionMatrixTwo.diffHalf
        ⟨buildTwo z.1.1 z.2 z.1.2, buildTwo_isHermitian z.1.1 z.2 z.1.2⟩) = z.1
      rw [diffHalf_buildTwo]
      show (z.1.1, z.1.2) = z.1
      rfl
    · show HermitianOctonionMatrixTwo.traceHalf
        ⟨buildTwo z.1.1 z.2 z.1.2, buildTwo_isHermitian z.1.1 z.2 z.1.2⟩ = z.2
      rw [traceHalf_buildTwo]
  map_mul' M N := by
    obtain ⟨r1, s1, hr1, hs1, hr1', hs1'⟩ :=
      HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf M
    obtain ⟨r2, s2, hr2, hs2, hr2', hs2'⟩ :=
      HermitianOctonionMatrixTwo.diag_eq_traceHalf_add_sub_diffHalf N
    set t1 := HermitianOctonionMatrixTwo.traceHalf M
    set p1 := HermitianOctonionMatrixTwo.diffHalf M
    set t2 := HermitianOctonionMatrixTwo.traceHalf N
    set p2 := HermitianOctonionMatrixTwo.diffHalf N
    set x1 := M.val 0 1 with hx1
    set x2 := N.val 0 1 with hx2
    have h10 : M.val 1 0 = star x1 := HermitianOctonionMatrixTwo.off_diag M
    have h20 : N.val 1 0 = star x2 := HermitianOctonionMatrixTwo.off_diag N
    have hmul : (M * N).val = (⅟2 : R) • (M.val * N.val + N.val * M.val) := rfl
    have hP01 : (M * N).val 0 1 = t1 • x2 + t2 • x1 := by
      show ((⅟2 : R) • (M.val * N.val + N.val * M.val)) 0 1 = t1 • x2 + t2 • x1
      show (⅟2 : R) • ((M.val * N.val) 0 1 + (N.val * M.val) 0 1) = t1 • x2 + t2 • x1
      have e1 : ⅟(2 : R) * (2 * t1) = t1 := by rw [← mul_assoc, invOf_mul_self, one_mul]
      have e2 : ⅟(2 : R) * (2 * t2) = t2 := by rw [← mul_assoc, invOf_mul_self, one_mul]
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [hr1, hs1, hr2, hs2]
      rw [scalarEmbed_mul, mul_scalarEmbed, scalarEmbed_mul, mul_scalarEmbed]
      rw [hr1', hs1', hr2', hs2']
      rw [show (t1 + p1) • x2 + (t2 - p2) • x1 + ((t2 + p2) • x1 + (t1 - p1) • x2) =
          (2 * t1) • x2 + (2 * t2) • x1 from by module]
      rw [smul_add, smul_smul, smul_smul, e1, e2]
    have hP00 : (M * N).val 0 0 = scalarEmbed (r1 * r2 + innerProduct x1 x2) := by
      show (⅟2 : R) • ((M.val * N.val) 0 0 + (N.val * M.val) 0 0) = _
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [hr1, hr2, h10, h20]
      have hkey : x1 * star x2 + x2 * star x1 = scalarEmbed (2 * innerProduct x1 x2) :=
        mul_star_add_star_mul_eq_scalarEmbed x1 x2
      have hsum : scalarEmbed r1 * scalarEmbed r2 + x1 * star x2 +
          (scalarEmbed r2 * scalarEmbed r1 + x2 * star x1) =
          scalarEmbed (r1 * r2 + r2 * r1 + 2 * innerProduct x1 x2) := by
        rw [map_add, map_add, map_mul, map_mul, ← hkey]
        abel
      rw [hsum, smul_scalarEmbed]
      congr 1
      have expand : r1 * r2 + r2 * r1 + 2 * innerProduct x1 x2 =
          2 * (r1 * r2 + innerProduct x1 x2) := by ring
      rw [expand, ← mul_assoc, invOf_mul_self, one_mul]
    have hP11 : (M * N).val 1 1 = scalarEmbed (s1 * s2 + innerProduct x1 x2) := by
      show (⅟2 : R) • ((M.val * N.val) 1 1 + (N.val * M.val) 1 1) = _
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [hs1, hs2, h10, h20]
      have hkey : star x1 * x2 + star x2 * x1 = scalarEmbed (2 * innerProduct (star x1) (star x2)) := by
        have := mul_star_add_star_mul_eq_scalarEmbed (star x1) (star x2)
        rwa [star_star, star_star] at this
      rw [innerProduct_star_star] at hkey
      have hsum : star x1 * x2 + scalarEmbed s1 * scalarEmbed s2 +
          (star x2 * x1 + scalarEmbed s2 * scalarEmbed s1) =
          scalarEmbed (s1 * s2 + s2 * s1 + 2 * innerProduct x1 x2) := by
        rw [map_add, map_add, map_mul, map_mul, ← hkey]
        abel
      rw [hsum, smul_scalarEmbed]
      congr 1
      have expand : s1 * s2 + s2 * s1 + 2 * innerProduct x1 x2 =
          2 * (s1 * s2 + innerProduct x1 x2) := by ring
      rw [expand, ← mul_assoc, invOf_mul_self, one_mul]
    apply SpinFactor.ext
    · show ((M * N).val 0 1, HermitianOctonionMatrixTwo.diffHalf (M * N)) = t1 • (x2, p2) + t2 • (x1, p1)
      apply Prod.ext
      · exact hP01
      · show HermitianOctonionMatrixTwo.diffHalf (M * N) = t1 * p2 + t2 * p1
        show ⅟(2 : R) * (((M * N).val 0 0).1.re - ((M * N).val 1 1).1.re) = t1 * p2 + t2 * p1
        rw [hP00, hP11, scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq,
          QuaternionAlgebra.algebraMap_eq]
        show ⅟(2 : R) * ((r1 * r2 + innerProduct x1 x2) - (s1 * s2 + innerProduct x1 x2)) =
          t1 * p2 + t2 * p1
        rw [hr1', hs1', hr2', hs2']
        rw [show ((t1 + p1) * (t2 + p2) + innerProduct x1 x2) -
            ((t1 - p1) * (t2 - p2) + innerProduct x1 x2) = 2 * (t1 * p2 + t2 * p1) from by ring,
          ← mul_assoc, invOf_mul_self, one_mul]
    · show HermitianOctonionMatrixTwo.traceHalf (M * N) =
        hermitianTwoBilin (R:=R) (a:=a) (b:=b) (c:=c) (x1, p1) (x2, p2) + t1 * t2
      show ⅟(2 : R) * (((M * N).val 0 0).1.re + ((M * N).val 1 1).1.re) = _
      rw [hP00, hP11, scalarEmbed_fst, scalarEmbed_fst, QuaternionAlgebra.algebraMap_eq,
        QuaternionAlgebra.algebraMap_eq]
      show ⅟(2 : R) * ((r1 * r2 + innerProduct x1 x2) + (s1 * s2 + innerProduct x1 x2)) =
        hermitianTwoBilinFun (x1, p1) (x2, p2) + t1 * t2
      show ⅟(2 : R) * ((r1 * r2 + innerProduct x1 x2) + (s1 * s2 + innerProduct x1 x2)) =
        (innerProduct x1 x2 + p1 * p2) + t1 * t2
      rw [hr1', hs1', hr2', hs2']
      rw [show ((t1 + p1) * (t2 + p2) + innerProduct x1 x2) +
          ((t1 - p1) * (t2 - p2) + innerProduct x1 x2) =
          2 * (innerProduct x1 x2 + p1 * p2 + t1 * t2) from by ring,
        ← mul_assoc, invOf_mul_self, one_mul]
  map_add' M N := by
    apply SpinFactor.ext
    · show ((M + N).val 0 1, HermitianOctonionMatrixTwo.diffHalf (M + N)) =
        (M.val 0 1, HermitianOctonionMatrixTwo.diffHalf M) +
          (N.val 0 1, HermitianOctonionMatrixTwo.diffHalf N)
      apply Prod.ext
      · rfl
      · show HermitianOctonionMatrixTwo.diffHalf (M + N) =
          HermitianOctonionMatrixTwo.diffHalf M + HermitianOctonionMatrixTwo.diffHalf N
        show ⅟(2 : R) * (((M + N).val 0 0).1.re - ((M + N).val 1 1).1.re) =
          ⅟(2 : R) * ((M.val 0 0).1.re - (M.val 1 1).1.re) +
            ⅟(2 : R) * ((N.val 0 0).1.re - (N.val 1 1).1.re)
        have h00 : ((M + N).val 0 0).1.re = (M.val 0 0).1.re + (N.val 0 0).1.re := rfl
        have h11 : ((M + N).val 1 1).1.re = (M.val 1 1).1.re + (N.val 1 1).1.re := rfl
        rw [h00, h11]
        ring
    · show HermitianOctonionMatrixTwo.traceHalf (M + N) =
        HermitianOctonionMatrixTwo.traceHalf M + HermitianOctonionMatrixTwo.traceHalf N
      show ⅟(2 : R) * (((M + N).val 0 0).1.re + ((M + N).val 1 1).1.re) =
        ⅟(2 : R) * ((M.val 0 0).1.re + (M.val 1 1).1.re) +
          ⅟(2 : R) * ((N.val 0 0).1.re + (N.val 1 1).1.re)
      have h00 : ((M + N).val 0 0).1.re = (M.val 0 0).1.re + (N.val 0 0).1.re := rfl
      have h11 : ((M + N).val 1 1).1.re = (M.val 1 1).1.re + (N.val 1 1).1.re := rfl
      rw [h00, h11]
      ring

end TwoByTwo

end Octonion
