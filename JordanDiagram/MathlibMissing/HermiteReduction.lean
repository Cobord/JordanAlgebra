module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Interval

/-!
# Hermite reduction of positive definite integral forms

For a symmetric integer matrix `A` indexed by `Option ι`, write `m = A none none` (`corner`),
`a = A (some ·) none` (`border`), `D = A (some ·) (some ·)` (`body`), and
`A' = m D - a aᵀ` (`schur`), an integer matrix indexed by `ι`.

* `corner_mul_quad`: `m · xᵀ A x = (m x₀ + a · y)² + yᵀ A' y` for `x = (x₀, y)`.
* `posQ_schur`: `A'` is positive definite when `A` is.
* `corner_mul_det_schur`: `m · det A' = m ^ #ι · det A`.
* `exists_unimodular_col`: a primitive integer vector is a column of a unimodular matrix (via the
  Smith normal form of the line it spans), and a minimal vector is primitive
  (`primitive_of_min`).
* `hermite`: **Hermite's inequality**. The minimum `m` of a positive definite integral form in
  `n + 1` variables satisfies `m ^ (n + 1) ≤ c_{n+1} · det A`, with `c_{n+1} = (4/3)ⁿ cₙ`
  (`hermiteConst`). Moving a minimal vector to the first basis vector, a rounding of the first
  coordinate gives `(3/4) m² ≤ min A'`, and induction applies to `A'`.
* `finite_classes`: **Hermite's finiteness theorem**. For each dimension and determinant,
  finitely many positive definite symmetric integer matrices represent all of them up to
  `A ↦ Pᵀ A P` with `P` unimodular. After moving a minimal vector to the first basis vector, a
  block-diagonal change `diag(1, U)` (`liftU`) puts `A'` in a finite set of representatives by
  induction, and a shear (`shear`) reduces the border modulo `m`. The matrix is then determined by
  `m`, the border and `A'` (`eq_build`), all in finite ranges.

## Source

This is the classical argument of Hermite, as in J. W. S. Cassels, *Rational Quadratic Forms*,
Academic Press, 1978, here with the integral Schur complement `m D - a aᵀ` so that every step stays
over `ℤ`.
-/

@[expose] public section

open Matrix

namespace Hermite

-- `[Fintype ι] [DecidableEq ι]` are section-wide, as most results need them (sums, determinants);
-- the few lemmas about entries alone do not.
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form of an integer matrix, evaluated on rational vectors. -/
def quad (A : Matrix ι ι ℤ) (v : ι → ℚ) : ℚ := v ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ v

/-- Positive definiteness over `ℚ`. -/
def PosQ (A : Matrix ι ι ℤ) : Prop := ∀ v : ι → ℚ, v ≠ 0 → 0 < quad A v

variable (A : Matrix (Option ι) (Option ι) ℤ)

/-- The corner entry `m = A none none`. -/
def corner : ℤ := A none none

/-- The border `a = A (some ·) none`. -/
def border : ι → ℤ := fun i => A (some i) none

/-- The body `D = A (some ·) (some ·)`. -/
def body : Matrix ι ι ℤ := fun i j => A (some i) (some j)

/-- The integral Schur complement `m D - a aᵀ`. -/
def schur : Matrix ι ι ℤ := corner A • body A - vecMulVec (border A) (border A)

/-- The vector `(x₀, y)` indexed by `Option ι`. -/
def joinVec {R : Type*} (x₀ : R) (y : ι → R) : Option ι → R := fun o => o.elim x₀ y

theorem quad_eq_sum (B : Matrix ι ι ℤ) (v : ι → ℚ) :
    quad B v = ∑ i, ∑ j, v i * (B i j : ℚ) * v j := by
  simp only [quad, dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The completed square**: `m · xᵀ A x = (m x₀ + a · y)² + yᵀ A' y`. -/
theorem corner_mul_quad (hA : A.IsSymm) (x₀ : ℚ) (y : ι → ℚ) :
    (corner A : ℚ) * quad A (joinVec x₀ y) =
      ((corner A : ℚ) * x₀ + ∑ i, (border A i : ℚ) * y i) ^ 2 + quad (schur A) y := by
  have hsym : ∀ i, (A none (some i) : ℚ) = border A i := fun i => by
    simp only [border]
    exact_mod_cast (hA.apply none (some i)).symm
  simp only [quad_eq_sum, Fintype.sum_option, joinVec, Option.elim_none, Option.elim_some, schur,
    Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, body, smul_eq_mul, Int.cast_sub,
    Int.cast_mul, hsym]
  simp only [corner, border, mul_sub, sub_mul, Finset.sum_sub_distrib, sq, Finset.sum_add_distrib]
  have hcross : ∀ i, ∑ j, y i * ((A (some i) none : ℚ) * A (some j) none) * y j =
      ∑ j, ((A (some i) none : ℚ) * y i) * ((A (some j) none : ℚ) * y j) := fun i =>
    Finset.sum_congr rfl fun j _ => by ring
  simp only [hcross]
  ring_nf
  set a : ι → ℚ := fun i => (A (some i) none : ℚ)
  have e1 : ∑ x, x₀ * a x * y x = x₀ * ∑ x, a x * y x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, x₀ * y x * a x = x₀ * ∑ x, a x * y x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, ∑ x_1, (A none none : ℚ) * y x * (A (some x) (some x_1)) * y x_1 =
      (A none none : ℚ) * ∑ x, ∑ x_1, y x * (A (some x) (some x_1) : ℚ) * y x_1 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e4 : ∑ x, ∑ x_1, a x * y x * a x_1 * y x_1 = (∑ x, a x * y x) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3, e4]
  ring

theorem joinVec_ne_zero {x₀ : ℚ} {y : ι → ℚ} (hy : y ≠ 0) : joinVec x₀ y ≠ 0 := fun h =>
  hy (funext fun i => congrFun h (some i))

theorem quad_joinVec_one_zero : quad A (joinVec 1 0) = A none none := by
  simp [quad_eq_sum, Fintype.sum_option, joinVec]

theorem corner_pos (hpos : PosQ A) : 0 < corner A := by
  have := hpos (joinVec 1 0) fun h => one_ne_zero (congrFun h none)
  rw [quad_joinVec_one_zero] at this
  exact_mod_cast this

/-- The Schur complement of a positive definite matrix is positive definite. -/
theorem posQ_schur (hA : A.IsSymm) (hpos : PosQ A) : PosQ (schur A) := by
  intro y hy
  have hm : (0 : ℚ) < corner A := by exact_mod_cast corner_pos A hpos
  set x₀ : ℚ := -(∑ i, (border A i : ℚ) * y i) / corner A
  have h := corner_mul_quad A hA x₀ y
  have hsq : (corner A : ℚ) * x₀ + ∑ i, (border A i : ℚ) * y i = 0 := by
    simp only [x₀]
    field_simp
    ring
  rw [hsq, sq, zero_mul, zero_add] at h
  rw [← h]
  exact mul_pos hm (hpos _ (joinVec_ne_zero hy))

theorem schur_isSymm (hA : A.IsSymm) : (schur A).IsSymm := by
  ext i j
  simp only [schur, transpose_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, body,
    smul_eq_mul]
  rw [hA.apply (some i) (some j), mul_comm (border A j)]

/-- **The determinant of the Schur complement**: `m · det A' = m ^ #ι · det A`. -/
theorem corner_mul_det_schur (hA : A.IsSymm) (hm : corner A ≠ 0) :
    corner A * (schur A).det = corner A ^ Fintype.card ι * A.det := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  change (corner A : ℚ) * ((Int.castRingHom ℚ).mapMatrix (schur A)).det =
    (corner A : ℚ) ^ Fintype.card ι * ((Int.castRingHom ℚ).mapMatrix A).det
  set m : ℚ := (corner A : ℚ)
  have hmq : m ≠ 0 := Int.cast_ne_zero.2 hm
  have hsym : ∀ j, A none (some j) = A (some j) none := fun j => (hA.apply none (some j)).symm
  set a : ι → ℚ := fun i => (border A i : ℚ)
  set Dq : Matrix ι ι ℚ := (body A).map (Int.cast : ℤ → ℚ)
  let e := Equiv.optionEquivSumPUnit.{0} ι
  let C : Matrix PUnit.{1} PUnit.{1} ℚ := of fun _ _ => m
  let hC : Invertible C := ⟨of fun _ _ => m⁻¹, by ext; simp [C, Matrix.mul_apply, hmq],
    by ext; simp [C, Matrix.mul_apply, hmq]⟩
  have hre : reindex e e ((Int.castRingHom ℚ).mapMatrix A) =
      fromBlocks Dq (of fun i _ => a i) (of fun _ j => a j) C := by
    ext (i | i) (j | j) <;>
      simp [e, C, Dq, a, m, body, border, corner, hsym]
  have hinv : ⅟C = of fun _ _ => m⁻¹ := rfl
  have hdet : ((Int.castRingHom ℚ).mapMatrix A).det = m * (Dq - m⁻¹ • vecMulVec a a).det := by
    rw [← det_reindex_self e, hre, det_fromBlocks₂₂, hinv]
    congr 1
    · simp [C]
    · congr 1
      ext i j
      simp [Matrix.mul_apply, vecMulVec_apply]
      ring
  have hschur : (Int.castRingHom ℚ).mapMatrix (schur A) = m • (Dq - m⁻¹ • vecMulVec a a) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, schur, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Dq, a, m, Int.cast_sub, Int.cast_mul,
      eq_intCast]
    rw [mul_sub, ← mul_assoc (corner A : ℚ), mul_inv_cancel₀ hmq, one_mul]
  rw [hschur, det_smul, hdet]
  ring

section Completion

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A vector is primitive when it is not a nonunit multiple of an integer vector. -/
def Primitive (x : κ → ℤ) : Prop := ∀ (k : ℤ) (w : κ → ℤ), x = k • w → IsUnit k

/-- **Completion to a basis**: a primitive vector is a column of a unimodular matrix. -/
theorem exists_unimodular_col {x : κ → ℤ} (hx0 : x ≠ 0) (hx : Primitive x) (o₀ : κ) :
    ∃ P : Matrix κ κ ℤ, IsUnit P.det ∧ ∀ k, P k o₀ = x k := by
  set N : Submodule ℤ (κ → ℤ) := Submodule.span ℤ {x}
  obtain ⟨n, S⟩ := N.smithNormalForm (Pi.basisFun ℤ κ)
  have hxN : x ∈ N := Submodule.mem_span_singleton_self x
  -- every basis vector of `N` is a multiple of `x`
  have hmul : ∀ i, ∃ c : ℤ, (S.bN i : κ → ℤ) = c • x := fun i =>
    (Submodule.mem_span_singleton.1 (S.bN i).2).imp fun c hc => hc.symm
  have hn : n = 1 := by
    have hpos : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this
      have := S.bN.repr.injective (a₁ := ⟨x, hxN⟩) (a₂ := 0) (Subsingleton.elim _ _)
      exact hx0 (congrArg Subtype.val this)
    by_contra h
    have h2 : 1 < n := by omega
    set i₀ : Fin n := ⟨0, hpos⟩
    set i₁ : Fin n := ⟨1, h2⟩
    have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    obtain ⟨c₀, hc₀⟩ := hmul i₀
    obtain ⟨c₁, hc₁⟩ := hmul i₁
    have hrel : c₁ • S.bN i₀ - c₀ • S.bN i₁ = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, Submodule.coe_smul, hc₀, hc₁, smul_smul, mul_comm c₁,
        sub_self, Submodule.coe_zero]
    have := congrArg (fun z => S.bN.repr z i₀) hrel
    simp only [map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne' hne.symm, smul_eq_mul, mul_one,
      mul_zero, sub_zero, map_zero, Finsupp.zero_apply] at this
    apply S.bN.ne_zero i₁
    apply Subtype.ext
    rw [hc₁, this, zero_smul, Submodule.coe_zero]
  subst hn
  -- `x` is a multiple of the single basis vector of `N`, hence of `bM (f 0)`
  have hx1 : x = (S.bN.repr ⟨x, hxN⟩ 0 * S.a 0) • S.bM (S.f 0) := by
    have := congrArg Subtype.val (S.bN.sum_repr ⟨x, hxN⟩)
    rw [Fin.sum_univ_one, Submodule.coe_smul, S.snf, smul_smul] at this
    exact this.symm
  obtain ⟨u, hu⟩ := hx _ _ hx1
  set j := S.f 0
  let b' := S.bM.unitsSMul fun i => if i = j then u else 1
  have hb'j : b' j = x := by
    simp only [b', Module.Basis.unitsSMul_apply, Units.smul_def, ite_true]
    rw [hu]
    exact hx1.symm
  let b'' := b'.reindex (Equiv.swap j o₀)
  have hb'' : b'' o₀ = x := by
    simp only [b'', Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right, hb'j]
  refine ⟨(Pi.basisFun ℤ κ).toMatrix b'', ?_, fun k => ?_⟩
  · let _ := (Pi.basisFun ℤ κ).invertibleToMatrix b''
    exact isUnit_det_of_invertible _
  · rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, hb'']

/-- Integer congruence: `A ↦ Pᵀ A P`. -/
def congrBy (P A : Matrix κ κ ℤ) : Matrix κ κ ℤ := Pᵀ * A * P

/-- The cast of an integer vector to a rational vector. -/
def toQ (w : κ → ℤ) : κ → ℚ := fun i => (w i : ℚ)

theorem toQ_injective : Function.Injective (toQ (κ := κ)) := fun _ _ h =>
  funext fun i => Int.cast_injective (congrFun h i)

theorem quad_congrBy (P A : Matrix κ κ ℤ) (v : κ → ℚ) :
    quad (congrBy P A) v = quad A (P.map (Int.cast : ℤ → ℚ) *ᵥ v) := by
  have hm : (Pᵀ * A * P).map (Int.cast : ℤ → ℚ) =
      (P.map (Int.cast : ℤ → ℚ))ᵀ * A.map (Int.cast : ℤ → ℚ) * P.map (Int.cast : ℤ → ℚ) := by
    have h1 := Matrix.map_mul (L := Pᵀ * A) (M := P) (f := Int.castRingHom ℚ)
    have h2 := Matrix.map_mul (L := Pᵀ) (M := A) (f := Int.castRingHom ℚ)
    simp only [Int.coe_castRingHom] at h1 h2
    rw [h1, h2, transpose_map]
  rw [quad, quad, congrBy, hm, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec v (P.map (Int.cast : ℤ → ℚ))ᵀ, vecMul_transpose]

theorem toQ_mulVec (P : Matrix κ κ ℤ) (w : κ → ℤ) :
    P.map (Int.cast : ℤ → ℚ) *ᵥ toQ w = toQ (P *ᵥ w) := by
  ext i
  simp [toQ, mulVec, dotProduct]

theorem quad_toQ (A : Matrix κ κ ℤ) (w : κ → ℤ) : quad A (toQ w) = ((w ⬝ᵥ A *ᵥ w : ℤ) : ℚ) := by
  simp [quad, toQ, dotProduct, mulVec, Finset.mul_sum]

theorem mulVec_ne_zero_of_isUnit {P : Matrix κ κ ℤ} (hP : IsUnit P.det) {v : κ → ℚ} (hv : v ≠ 0) :
    P.map (Int.cast : ℤ → ℚ) *ᵥ v ≠ 0 := by
  have hdet : (P.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [show P.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix P from rfl,
      ← RingHom.map_det]
    exact Int.cast_ne_zero.2 hP.ne_zero
  intro h
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, h⟩)

theorem posQ_congrBy {P A : Matrix κ κ ℤ} (hP : IsUnit P.det) (hA : PosQ A) :
    PosQ (congrBy P A) := fun v hv => by
  rw [quad_congrBy]
  exact hA _ (mulVec_ne_zero_of_isUnit hP hv)

theorem isSymm_congrBy {P A : Matrix κ κ ℤ} (hA : A.IsSymm) : (congrBy P A).IsSymm := by
  simp only [congrBy, IsSymm, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]

theorem det_congrBy {P A : Matrix κ κ ℤ} (hP : IsUnit P.det) : (congrBy P A).det = A.det := by
  rw [congrBy, det_mul, det_mul, det_transpose]
  rcases Int.isUnit_iff.1 hP with h | h <;> rw [h] <;> ring

theorem congrBy_apply_eq_quad (P A : Matrix κ κ ℤ) (o : κ) :
    (congrBy P A o o : ℚ) = quad A (toQ fun k => P k o) := by
  rw [quad_eq_sum]
  simp only [congrBy, Matrix.mul_apply, transpose_apply, Finset.sum_mul, Int.cast_sum,
    Int.cast_mul, toQ]
  rw [Finset.sum_comm]

theorem quad_smul (A : Matrix κ κ ℤ) (k : ℤ) (w : κ → ℤ) :
    quad A (toQ (k • w)) = (k : ℚ) ^ 2 * quad A (toQ w) := by
  simp only [quad_eq_sum, toQ, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem toQ_ne_zero {w : κ → ℤ} (hw : w ≠ 0) : toQ w ≠ 0 := fun h =>
  hw (funext fun i => by simpa [toQ] using congrFun h i)

theorem quad_toQ_nonneg_int (A : Matrix κ κ ℤ) (hA : PosQ A) (w : κ → ℤ) :
    ∃ n : ℕ, quad A (toQ w) = n := by
  rw [quad_toQ]
  have h0 : 0 ≤ w ⬝ᵥ A *ᵥ w := by
    by_cases hw : w = 0
    · simp [hw]
    · have := hA _ (toQ_ne_zero hw)
      rw [quad_toQ] at this
      exact_mod_cast this.le
  refine ⟨(w ⬝ᵥ A *ᵥ w).toNat, ?_⟩
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

/-- A positive definite form attains its minimum on nonzero integer vectors. -/
theorem exists_min [Nonempty κ] (A : Matrix κ κ ℤ) (hA : PosQ A) :
    ∃ x₀ : κ → ℤ, x₀ ≠ 0 ∧ ∀ w : κ → ℤ, w ≠ 0 → quad A (toQ x₀) ≤ quad A (toQ w) := by
  classical
  have hex : ∃ n : ℕ, ∃ w : κ → ℤ, w ≠ 0 ∧ quad A (toQ w) = n := by
    obtain ⟨i⟩ := ‹Nonempty κ›
    have hw : (Pi.single i 1 : κ → ℤ) ≠ 0 := fun h =>
      (one_ne_zero : (1 : ℤ) ≠ 0) (by simpa using congrFun h i)
    obtain ⟨n, hn⟩ := quad_toQ_nonneg_int A hA (Pi.single i 1)
    exact ⟨n, _, hw, hn⟩
  obtain ⟨x₀, hx₀, hval⟩ := Nat.find_spec hex
  refine ⟨x₀, hx₀, fun w hw => ?_⟩
  obtain ⟨n, hn⟩ := quad_toQ_nonneg_int A hA w
  rw [hval, hn]
  exact_mod_cast Nat.find_min' hex ⟨w, hw, hn⟩

/-- A vector minimizing a positive definite form is primitive. -/
theorem primitive_of_min {A : Matrix κ κ ℤ} (hA : PosQ A) {x₀ : κ → ℤ} (hx₀ : x₀ ≠ 0)
    (hmin : ∀ w : κ → ℤ, w ≠ 0 → quad A (toQ x₀) ≤ quad A (toQ w)) : Primitive x₀ := by
  intro k w hkw
  have hw : w ≠ 0 := fun h => hx₀ (by rw [hkw, h, smul_zero])
  have hk : k ≠ 0 := fun h => hx₀ (by rw [hkw, h, zero_smul])
  have hq := hmin w hw
  rw [hkw, quad_smul] at hq
  have hpos : 0 < quad A (toQ w) :=
    hA _ fun h => hw (toQ_injective (by rw [h]; ext; simp [toQ]))
  have hk2 : (k : ℚ) ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hk2' : k ^ 2 ≤ 1 := by exact_mod_cast hk2
  have : k = 1 ∨ k = -1 := by
    have h1 : -1 ≤ k := by nlinarith
    have h2 : k ≤ 1 := by nlinarith
    omega
  rcases this with rfl | rfl
  · exact isUnit_one
  · exact isUnit_one.neg

end Completion

/-- **Rounding**: for `m > 0` and any `s`, some `t` has `4 (m t + s)² ≤ m²`. -/
theorem exists_round {m : ℤ} (hm : 0 < m) (s : ℤ) : ∃ t : ℤ, 4 * (m * t + s) ^ 2 ≤ m ^ 2 := by
  have hr0 := Int.emod_nonneg s hm.ne'
  have hr1 := Int.emod_lt_of_pos s hm
  have hs := Int.emod_add_mul_ediv s m
  by_cases h : 2 * (s % m) ≤ m
  · refine ⟨-(s / m), ?_⟩
    have : m * -(s / m) + s = s % m := by linarith
    rw [this]
    nlinarith
  · refine ⟨-(s / m) - 1, ?_⟩
    have : m * (-(s / m) - 1) + s = s % m - m := by linarith
    rw [this]
    nlinarith

section Reindex

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)

theorem quad_reindex (A : Matrix α α ℤ) (v : β → ℚ) :
    quad (reindex e e A) v = quad A (v ∘ e) := by
  simp only [quad_eq_sum, reindex_apply, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← e.sum_comp]
    simp

theorem posQ_reindex {A : Matrix α α ℤ} (hA : PosQ A) : PosQ (reindex e e A) := fun v hv => by
  rw [quad_reindex]
  exact hA _ fun h => hv (funext fun b => by simpa using congrFun h (e.symm b))

theorem isSymm_reindex {A : Matrix α α ℤ} (hA : A.IsSymm) : (reindex e e A).IsSymm := by
  ext i j
  simp only [transpose_apply, reindex_apply, submatrix_apply]
  exact hA.apply _ _

end Reindex

theorem joinVec_toQ (t : ℤ) (y : ι → ℤ) : joinVec (t : ℚ) (toQ y) = toQ (joinVec t y) := by
  funext o
  cases o <;> rfl

/-- The constants in Hermite's inequality, `c₁ = 1` and `c_{n+1} = (4/3)ⁿ cₙ`. -/
def hermiteConst : ℕ → ℚ
  | 0 => 1
  | n + 1 => (4 / 3) ^ n * hermiteConst n

/-- Moving a minimal vector to the first basis vector. -/
theorem exists_reduce {A : Matrix (Option ι) (Option ι) ℤ} (hpos : PosQ A)
    {x₀ : Option ι → ℤ} (hx₀ : x₀ ≠ 0)
    (hmin : ∀ w : Option ι → ℤ, w ≠ 0 → quad A (toQ x₀) ≤ quad A (toQ w)) :
    ∃ P : Matrix (Option ι) (Option ι) ℤ, IsUnit P.det ∧
      (corner (congrBy P A) : ℚ) = quad A (toQ x₀) ∧
      ∀ w : Option ι → ℤ, w ≠ 0 → quad A (toQ x₀) ≤ quad (congrBy P A) (toQ w) := by
  obtain ⟨P, hP, hcol⟩ := exists_unimodular_col hx₀ (primitive_of_min hpos hx₀ hmin) none
  refine ⟨P, hP, ?_, fun w hw => ?_⟩
  · rw [corner, congrBy_apply_eq_quad]
    congr 2
    exact funext hcol
  · rw [quad_congrBy, toQ_mulVec]
    refine hmin _ fun h => ?_
    apply mulVec_ne_zero_of_isUnit hP (toQ_ne_zero hw)
    rw [toQ_mulVec, h]
    funext i
    simp [toQ]

/-- **Hermite's inequality**: the minimum `m` of a positive definite integral form in `n + 1`
variables satisfies `m ^ (n + 1) ≤ c_{n+1} · det A`. -/
theorem hermite (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ A : Matrix (Option ι) (Option ι) ℤ, A.IsSymm → PosQ A → ∀ x₀ : Option ι → ℤ, x₀ ≠ 0 →
      (∀ w : Option ι → ℤ, w ≠ 0 → quad A (toQ x₀) ≤ quad A (toQ w)) →
      quad A (toQ x₀) ^ (n + 1) ≤ hermiteConst (n + 1) * A.det := by
  induction n with
  | zero =>
    intro ι _ _ hcard A hA hpos x₀ hx₀ hmin
    obtain ⟨P, hP, hcorner, -⟩ := exists_reduce hpos hx₀ hmin
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
    have hdet := corner_mul_det_schur (congrBy P A) (isSymm_congrBy hA)
      (corner_pos _ (posQ_congrBy hP hpos)).ne'
    rw [det_isEmpty, mul_one, hcard, pow_zero, one_mul, det_congrBy hP] at hdet
    rw [← hcorner, hdet]
    simp [hermiteConst]
  | succ n ih =>
    intro ι _ _ hcard A hA hpos x₀ hx₀ hmin
    obtain ⟨P, hP, hcorner, hminB⟩ := exists_reduce hpos hx₀ hmin
    set B := congrBy P A
    have hBs : B.IsSymm := isSymm_congrBy hA
    have hBp : PosQ B := posQ_congrBy hP hpos
    have hm : 0 < corner B := corner_pos B hBp
    set m : ℚ := (corner B : ℚ)
    have hmq : 0 < m := Int.cast_pos.2 hm
    let e : ι ≃ Option (Fin n) := Fintype.equivOfCardEq (by simp [hcard])
    set A' := schur B
    have hA's : A'.IsSymm := schur_isSymm B hBs
    have hA'p : PosQ A' := posQ_schur B hBs hBp
    obtain ⟨y₀, hy₀, hy₀min⟩ := exists_min (reindex e e A') (posQ_reindex e hA'p)
    have hIH := ih (Fin n) (by simp) (reindex e e A') (isSymm_reindex e hA's)
      (posQ_reindex e hA'p) y₀ hy₀ hy₀min
    rw [det_reindex_self] at hIH
    set y : ι → ℤ := y₀ ∘ e
    have hy : y ≠ 0 := fun h => hy₀ (funext fun b => by simpa [y] using congrFun h (e.symm b))
    have hq' : quad (reindex e e A') (toQ y₀) = quad A' (toQ y) := by
      rw [quad_reindex]
      rfl
    rw [hq'] at hIH
    set q' := quad A' (toQ y)
    -- rounding the first coordinate
    set s : ℤ := ∑ i, border B i * y i
    obtain ⟨t, ht⟩ := exists_round hm s
    have hw : joinVec t y ≠ 0 := fun h => hy (funext fun i => by
      simpa [joinVec] using congrFun h (some i))
    have hle := hminB _ hw
    rw [← hcorner, ← joinVec_toQ] at hle
    have hid := corner_mul_quad B hBs (t : ℚ) (toQ y)
    have hs : (m * t + ∑ i, (border B i : ℚ) * toQ y i) = ((corner B * t + s : ℤ) : ℚ) := by
      simp [s, toQ, m]
    rw [hs] at hid
    have ht' : 4 * ((corner B * t + s : ℤ) : ℚ) ^ 2 ≤ m ^ 2 := by
      have := (Int.cast_le (R := ℚ)).2 ht
      push_cast at this ⊢
      exact this
    have hq : 3 / 4 * m ^ 2 ≤ q' := by nlinarith
    -- the determinant of the Schur complement
    have hdet := corner_mul_det_schur B hBs hm.ne'
    rw [hcard, det_congrBy hP] at hdet
    have hdetq : m * (A'.det : ℚ) = m ^ (n + 1) * A.det := by
      have := congrArg (Int.cast : ℤ → ℚ) hdet
      simp only [Int.cast_mul, Int.cast_pow] at this
      exact this
    have h1 : (3 / 4 * m ^ 2) ^ (n + 1) ≤ q' ^ (n + 1) :=
      pow_le_pow_left₀ (by positivity) hq _
    have h2 : (3 / 4) ^ (n + 1) * m ^ (n + 1) * (m * m ^ (n + 1)) ≤
        hermiteConst (n + 1) * A.det * m ^ (n + 1) := by
      have := mul_le_mul_of_nonneg_left (h1.trans hIH) hmq.le
      calc (3 / 4) ^ (n + 1) * m ^ (n + 1) * (m * m ^ (n + 1))
          = m * (3 / 4 * m ^ 2) ^ (n + 1) := by ring
        _ ≤ m * (hermiteConst (n + 1) * A'.det) := this
        _ = hermiteConst (n + 1) * (m * A'.det) := by ring
        _ = hermiteConst (n + 1) * A.det * m ^ (n + 1) := by rw [hdetq]; ring
    have h3 : (3 / 4) ^ (n + 1) * (m * m ^ (n + 1)) ≤ hermiteConst (n + 1) * A.det := by
      have hpow : 0 < m ^ (n + 1) := by positivity
      nlinarith
    rw [← hcorner]
    calc m ^ (n + 1 + 1) = (4 / 3) ^ (n + 1) * ((3 / 4) ^ (n + 1) * (m * m ^ (n + 1))) := by
          rw [← mul_assoc, ← mul_pow]; norm_num; ring
      _ ≤ (4 / 3) ^ (n + 1) * (hermiteConst (n + 1) * A.det) := by gcongr
      _ = hermiteConst (n + 1 + 1) * A.det := by simp [hermiteConst]; ring

section Blocks

/-- The block-diagonal matrix `diag(1, U)`. -/
def liftU (U : Matrix ι ι ℤ) : Matrix (Option ι) (Option ι) ℤ
  | none, none => 1
  | some i, some j => U i j
  | _, _ => 0

/-- The shear `x₀ ↦ x₀ + t · y`. -/
def shear (t : ι → ℤ) : Matrix (Option ι) (Option ι) ℤ
  | none, none => 1
  | none, some j => t j
  | some i, some j => if i = j then 1 else 0
  | some _, none => 0

theorem liftU_mul (U V : Matrix ι ι ℤ) : liftU U * liftU V = liftU (U * V) := by
  ext (_ | i) (_ | j) <;> simp [liftU, Matrix.mul_apply, Fintype.sum_option]

theorem liftU_one : liftU (1 : Matrix ι ι ℤ) = 1 := by
  ext (_ | i) (_ | j) <;> simp [liftU, Matrix.one_apply]

theorem shear_mul (t t' : ι → ℤ) : shear t * shear t' = shear (t + t') := by
  ext (_ | i) (_ | j) <;>
    simp [shear, Matrix.mul_apply, Fintype.sum_option, add_comm]

theorem shear_zero : shear (0 : ι → ℤ) = 1 := by
  ext (_ | i) (_ | j) <;> simp [shear, Matrix.one_apply]

theorem isUnit_det_of_mul_eq_one {M N : Matrix (Option ι) (Option ι) ℤ} (h : M * N = 1) :
    IsUnit M.det :=
  IsUnit.of_mul_eq_one N.det (by rw [← det_mul, h, det_one])

theorem isUnit_det_liftU {U : Matrix ι ι ℤ} (hU : IsUnit U.det) : IsUnit (liftU U).det :=
  isUnit_det_of_mul_eq_one (N := liftU U⁻¹) (by rw [liftU_mul, mul_nonsing_inv _ hU, liftU_one])

theorem isUnit_det_shear (t : ι → ℤ) : IsUnit (shear t).det :=
  isUnit_det_of_mul_eq_one (N := shear (-t)) (by rw [shear_mul, add_neg_cancel, shear_zero])

variable (B : Matrix (Option ι) (Option ι) ℤ)

theorem corner_liftU (U : Matrix ι ι ℤ) : corner (congrBy (liftU U) B) = corner B := by
  simp [corner, congrBy, liftU, Matrix.mul_apply, Fintype.sum_option]

theorem border_liftU (U : Matrix ι ι ℤ) (i : ι) :
    border (congrBy (liftU U) B) i = ∑ k, U k i * border B k := by
  simp [border, congrBy, liftU, Matrix.mul_apply, Fintype.sum_option]

theorem body_liftU (U : Matrix ι ι ℤ) (i j : ι) :
    body (congrBy (liftU U) B) i j = ∑ k, ∑ l, U k i * body B k l * U l j := by
  simp [body, congrBy, liftU, Matrix.mul_apply, Fintype.sum_option, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem schur_liftU (U : Matrix ι ι ℤ) : schur (congrBy (liftU U) B) = congrBy U (schur B) := by
  ext i j
  set S := schur B
  have hL : schur (congrBy (liftU U) B) i j = ∑ k, ∑ l, U k i * S k l * U l j := by
    simp only [schur, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      corner_liftU, border_liftU, body_liftU, S]
    rw [Finset.mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hR : congrBy U S i j = ∑ k, ∑ l, U k i * S k l * U l j := by
    simp only [congrBy, Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hL, hR]

theorem corner_shear (t : ι → ℤ) : corner (congrBy (shear t) B) = corner B := by
  simp [corner, congrBy, shear, Matrix.mul_apply, Fintype.sum_option]

theorem border_shear (t : ι → ℤ) (i : ι) :
    border (congrBy (shear t) B) i = border B i + corner B * t i := by
  simp [border, corner, congrBy, shear, Matrix.mul_apply, Fintype.sum_option, Finset.sum_ite_eq']
  ring

theorem body_shear (hB : B.IsSymm) (t : ι → ℤ) (i j : ι) :
    body (congrBy (shear t) B) i j =
      body B i j + t i * border B j + border B i * t j + corner B * t i * t j := by
  have hs : ∀ k, B none (some k) = border B k := fun k => (hB.apply none (some k)).symm
  simp [body, border, corner, congrBy, shear, Matrix.mul_apply, Fintype.sum_option,
    Finset.sum_ite_eq', hs]
  ring

theorem schur_shear (hB : B.IsSymm) (t : ι → ℤ) : schur (congrBy (shear t) B) = schur B := by
  ext i j
  simp only [schur, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    corner_shear, border_shear B, body_shear B hB]
  ring

/-- The symmetric matrix with corner `m`, border `a` and integral Schur complement `R`. -/
def build (m : ℤ) (a : ι → ℤ) (R : Matrix ι ι ℤ) : Matrix (Option ι) (Option ι) ℤ
  | none, none => m
  | none, some j => a j
  | some i, none => a i
  | some i, some j => (R i j + a i * a j) / m

/-- A symmetric matrix is determined by its corner, border and integral Schur complement. -/
theorem eq_build (hB : B.IsSymm) (hm : corner B ≠ 0) :
    B = build (corner B) (border B) (schur B) := by
  ext (_ | i) (_ | j)
  · rfl
  · exact hB.apply none (some j) |>.symm
  · rfl
  · simp only [build, schur, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      body, sub_add_cancel]
    exact (Int.mul_ediv_cancel_left _ hm).symm

end Blocks

section Finiteness

theorem congrBy_congrBy {κ : Type*} [Fintype κ] (P Q A : Matrix κ κ ℤ) :
    congrBy Q (congrBy P A) = congrBy (P * Q) A := by
  simp only [congrBy, transpose_mul, Matrix.mul_assoc]

theorem reindex_congrBy {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (P A : Matrix α α ℤ) :
    reindex e e (congrBy P A) = congrBy (reindex e e P) (reindex e e A) := by
  simp only [congrBy, reindex_apply, transpose_submatrix, submatrix_mul_equiv]

/-- **Hermite's finiteness theorem**: for each dimension `n` and determinant `d`, finitely many
positive definite symmetric integer matrices represent every one up to `A ↦ Pᵀ A P` with `P`
unimodular. -/
theorem finite_classes (n : ℕ) (d : ℤ) : ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ),
    ∀ A : Matrix (Fin n) (Fin n) ℤ, A.IsSymm → PosQ A → A.det = d →
      ∃ P : Matrix (Fin n) (Fin n) ℤ, IsUnit P.det ∧ congrBy P A ∈ S := by
  induction n generalizing d with
  | zero => exact ⟨{1}, fun A _ _ _ => ⟨1, by simp, Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩⟩
  | succ n ih =>
    choose Sf hSf using ih
    let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv n
    set M : ℤ := ⌈hermiteConst (n + 1) * d⌉
    refine ⟨(Finset.Icc 1 M).biUnion fun m =>
      (Finset.univ : Finset (Fin n → Fin m.toNat)).biUnion fun a =>
        (Sf ((m ^ n * d) / m)).image fun R =>
          reindex e.symm e.symm (build m (fun i => ((a i : ℕ) : ℤ)) R), ?_⟩
    intro A hA hpos hdet
    set C := reindex e e A
    have hCs : C.IsSymm := isSymm_reindex e hA
    have hCp : PosQ C := posQ_reindex e hpos
    have hCd : C.det = d := by rw [det_reindex_self, hdet]
    obtain ⟨x₀, hx₀, hmin⟩ := exists_min C hCp
    obtain ⟨P, hP, hcorner, -⟩ := exists_reduce hCp hx₀ hmin
    have hherm := hermite n (Fin n) (by simp) C hCs hCp x₀ hx₀ hmin
    set B := congrBy P C
    have hBs : B.IsSymm := isSymm_congrBy hCs
    have hBp : PosQ B := posQ_congrBy hP hCp
    set m := corner B
    have hm : 0 < m := corner_pos B hBp
    have hmM : m ≤ M := by
      rw [← hcorner, hCd] at hherm
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      have h1 : (m : ℚ) ≤ (m : ℚ) ^ (n + 1) := le_self_pow₀ hm1 (by omega)
      have h2 : (m : ℚ) ≤ (M : ℚ) := (h1.trans hherm).trans (Int.le_ceil _)
      exact_mod_cast h2
    -- the Schur complement and its representative
    set A' := schur B
    have hA's : A'.IsSymm := schur_isSymm B hBs
    have hA'p : PosQ A' := posQ_schur B hBs hBp
    have hA'd : A'.det = (m ^ n * d) / m := by
      have h := corner_mul_det_schur B hBs hm.ne'
      rw [Fintype.card_fin, det_congrBy hP, hCd] at h
      exact Int.eq_ediv_of_mul_eq_right hm.ne' h
    obtain ⟨U, hU, hR⟩ := hSf _ A' hA's hA'p hA'd
    set B₁ := congrBy (liftU U) B
    have hB₁s : B₁.IsSymm := isSymm_congrBy hBs
    set t : Fin n → ℤ := fun i => -(border B₁ i / m)
    set B₂ := congrBy (shear t) B₁
    have hB₂s : B₂.IsSymm := isSymm_congrBy hB₁s
    have hc₂ : corner B₂ = m := by rw [corner_shear, corner_liftU]
    have hs₂ : schur B₂ = congrBy U A' := by rw [schur_shear B₁ hB₁s, schur_liftU]
    have hb₂ : ∀ i, border B₂ i = border B₁ i % m := fun i => by
      rw [border_shear B₁, corner_liftU, Int.emod_def]
      simp [t]
      ring
    have hb₂0 : ∀ i, 0 ≤ border B₂ i := fun i => by rw [hb₂]; exact Int.emod_nonneg _ hm.ne'
    have hb₂1 : ∀ i, border B₂ i < m := fun i => by rw [hb₂]; exact Int.emod_lt_of_pos _ hm
    have hbuild : B₂ = build m (border B₂) (congrBy U A') := by
      rw [← hc₂, ← hs₂]
      exact eq_build B₂ hB₂s (by rw [hc₂]; exact hm.ne')
    set Q := P * liftU U * shear t
    have hQ : IsUnit Q.det := by
      simp only [Q, det_mul]
      exact (hP.mul (isUnit_det_liftU hU)).mul (isUnit_det_shear t)
    have hB₂Q : B₂ = congrBy Q C := by
      simp only [B₂, B₁, B, Q, congrBy_congrBy, Matrix.mul_assoc]
    refine ⟨reindex e.symm e.symm Q, by rw [det_reindex_self]; exact hQ, ?_⟩
    have hA : reindex e.symm e.symm C = A := by ext i j; simp [C]
    rw [← hA, ← reindex_congrBy, ← hB₂Q, hbuild]
    refine Finset.mem_biUnion.2 ⟨m, Finset.mem_Icc.2 ⟨hm, hmM⟩, Finset.mem_biUnion.2
      ⟨fun i => ⟨(border B₂ i).toNat, ?_⟩, Finset.mem_univ _, Finset.mem_image.2
        ⟨_, hR, ?_⟩⟩⟩
    · have := hb₂1 i
      omega
    · congr 2
      funext i
      simp [Int.toNat_of_nonneg (hb₂0 i)]

end Finiteness

end Hermite
