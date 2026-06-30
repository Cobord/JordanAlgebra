import Jordan.JordanAlgebra
import Jordan.FormallyReal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.SumFourSquares

/-!
# Spin factor Jordan algebras

Given a module `V` over a commutative ring `R` together with a symmetric bilinear form `B` on
`V`, the *spin factor* is `V × R` equipped with the Jordan product

`(x, a) ∘ (y, b) = (a • y + b • x, B x y + a * b)`.

This is one of the classical families of (formally real, when `R = ℝ` and `B` is positive
definite) Jordan algebras, alongside the Hermitian-matrix examples in `RealQM`, `ComplexQM`, and
`QuaternionicQM`. Unlike those, it needs no hypothesis like `2` invertible: the construction and
the Jordan identity both hold over any commutative ring.
-/

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The spin factor Jordan algebra on `V × R` determined by a symmetric bilinear form `B` on `V`.
A type synonym for `V × R`, kept distinct so that the Jordan-product `Mul` instance below (which
depends on `B`) doesn't clash with instances coming from a different choice of form. -/
def SpinFactor (_B : LinearMap.BilinForm R V) : Type _ := V × R

namespace SpinFactor

variable {R V}
variable (B : LinearMap.BilinForm R V)

instance : AddCommGroup (SpinFactor R V B) := (inferInstance : AddCommGroup (V × R))
instance : Module R (SpinFactor R V B) := (inferInstance : Module R (V × R))

@[ext] theorem ext {z w : SpinFactor R V B} (h1 : z.1 = w.1) (h2 : z.2 = w.2) : z = w :=
  Prod.ext h1 h2

@[simp] theorem add_fst (z w : SpinFactor R V B) : (z + w).1 = z.1 + w.1 := rfl
@[simp] theorem add_snd (z w : SpinFactor R V B) : (z + w).2 = z.2 + w.2 := rfl
@[simp] theorem zero_fst : (0 : SpinFactor R V B).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : SpinFactor R V B).2 = 0 := rfl
@[simp] theorem smul_fst (r : R) (z : SpinFactor R V B) : (r • z).1 = r • z.1 := rfl
@[simp] theorem smul_snd (r : R) (z : SpinFactor R V B) : (r • z).2 = r • z.2 := rfl

/-- Build a spin factor element from its vector and scalar parts. -/
def mk (x : V) (a : R) : SpinFactor R V B := (x, a)

@[simp] theorem mk_fst (x : V) (a : R) : (mk B x a).1 = x := rfl
@[simp] theorem mk_snd (x : V) (a : R) : (mk B x a).2 = a := rfl

instance : Mul (SpinFactor R V B) where
  mul z w := mk B (z.2 • w.1 + w.2 • z.1) (B z.1 w.1 + z.2 * w.2)

@[simp] theorem mul_fst (z w : SpinFactor R V B) : (z * w).1 = z.2 • w.1 + w.2 • z.1 := rfl
@[simp] theorem mul_snd (z w : SpinFactor R V B) : (z * w).2 = B z.1 w.1 + z.2 * w.2 := rfl

instance : One (SpinFactor R V B) := ⟨mk B 0 1⟩

@[simp] theorem one_fst : (1 : SpinFactor R V B).1 = 0 := rfl
@[simp] theorem one_snd : (1 : SpinFactor R V B).2 = 1 := rfl

instance : NonAssocRing (SpinFactor R V B) where
  left_distrib z w v := by ext <;> simp [smul_add, mul_add] <;> [module; ring]
  right_distrib z w v := by ext <;> simp [add_smul, map_add, add_mul] <;> [module; ring]
  zero_mul z := by ext <;> simp
  mul_zero z := by ext <;> simp
  one_mul z := by ext <;> simp
  mul_one z := by ext <;> simp

theorem spinFactor_mul_comm (hB : B.IsSymm) (z w : SpinFactor R V B) : z * w = w * z := by
  ext <;> simp [hB.eq, add_comm]
  ring

instance : IsScalarTower R (SpinFactor R V B) (SpinFactor R V B) where
  smul_assoc r z w := by
    ext <;> simp [smul_add, smul_smul] <;> ring_nf

instance : SMulCommClass R (SpinFactor R V B) (SpinFactor R V B) where
  smul_comm r z w := by
    ext <;> simp [smul_add, smul_smul, mul_comm]
    ring

/-- The spin factor of a symmetric bilinear form is a Jordan algebra. -/
@[reducible]
noncomputable def jordanAlgebra (hB : B.IsSymm) : JordanAlgebra R (SpinFactor R V B) :=
  { (inferInstance : NonAssocRing (SpinFactor R V B)),
    (inferInstance : Module R (SpinFactor R V B)),
    (inferInstance : IsScalarTower R (SpinFactor R V B) (SpinFactor R V B)),
    (inferInstance : SMulCommClass R (SpinFactor R V B) (SpinFactor R V B)) with
    jordan_mul_comm := spinFactor_mul_comm B hB
    jordan_identity := fun z w => by
      obtain ⟨x, a⟩ := z
      obtain ⟨y, b⟩ := w
      ext <;> simp <;> [module; ring]
  }

/-- The vector-part projection `SpinFactor R V B →ₗ[R] V`, as a linear map (so it commutes with
finite sums). -/
def fstLinear : SpinFactor R V B →ₗ[R] V where
  toFun z := z.1
  map_add' := add_fst B
  map_smul' := smul_fst B

@[simp] theorem fstLinear_apply (z : SpinFactor R V B) : fstLinear B z = z.1 := rfl

/-- The scalar-part projection `SpinFactor R V B →ₗ[R] R`, as a linear map (so it commutes with
finite sums). -/
def sndLinear : SpinFactor R V B →ₗ[R] R where
  toFun z := z.2
  map_add' := add_snd B
  map_smul' := smul_snd B

@[simp] theorem sndLinear_apply (z : SpinFactor R V B) : sndLinear B z = z.2 := rfl

section Determinant

/-- The spin-factor determinant (norm form) `Δ(x, a) = a * a - B x x`. This is the degree-`2`
form for which every `z : SpinFactor R V B` satisfies its own "Cayley-Hamilton" relation
`z * z - τ(z) • z + Δ(z) • 1 = 0` for the linear trace `τ(z) = 2 * z.2` (the classical structure
of a rank-`2` Jordan algebra), though we don't need that fact here -- just the quadratic form
itself, which makes sense over any commutative ring `R`. -/
def determinant : QuadraticMap R (SpinFactor R V B) R :=
  QuadraticMap.sq.comp (sndLinear B) - B.toQuadraticMap.comp (fstLinear B)

@[simp] theorem determinant_apply (z : SpinFactor R V B) :
    determinant B z = z.2 * z.2 - B z.1 z.1 := by
  simp [determinant]

/-- The ring-agnostic substitute for "`z` lies on the boundary of the cone of squares": without an
order on `R` there's no topological boundary to speak of, but `Δ(z) = 0` is still exactly the
algebraic condition for `z` to be *rank `≤ 1`*, i.e. to satisfy the *linear* self-multiplication
relation `z * z = τ(z) • z` (with `τ(z) = 2 * z.2` the linear trace) instead of needing the
generic rank-`2` relation `z * z = τ(z) • z - Δ(z) • 1`. -/
theorem mul_self_eq_smul_iff (z : SpinFactor R V B) :
    z * z = (2 * z.2) • z ↔ determinant B z = 0 := by
  rw [determinant_apply, sub_eq_zero]
  constructor
  · intro h
    have h2 : (z * z).2 = ((2 * z.2) • z).2 := congrArg Prod.snd h
    simp only [mul_snd, smul_snd, smul_eq_mul] at h2
    linear_combination -h2
  · intro h
    apply SpinFactor.ext
    · simp only [mul_fst, smul_fst, add_fst, two_mul, add_smul]
    · simp only [mul_snd, smul_snd, smul_eq_mul]
      linear_combination -h

end Determinant

section NullVector

theorem not_isFormallyReal_of_nullVector (hB : B.IsSymm) {v : V} (hv : v ≠ 0)
    (hnull : B v v = 0) :
    ¬ @IsFormallyReal R (SpinFactor R V B) _ (jordanAlgebra B hB) := by
  letI : JordanAlgebra R (SpinFactor R V B) := jordanAlgebra B hB
  let z : SpinFactor R V B := mk B v 0
  apply IsFormallyReal.not_of_exists_mul_self_eq_zero (x := z)
  · intro hz
    exact hv (by simpa [z] using congrArg Prod.fst hz)
  have hzsq : z * z = 0 := by
    ext <;> simp [z, hnull]
  exact hzsq

end NullVector

/-! ### Formal reality under positivity

For `R` an ordered commutative ring (not necessarily a field -- it could be an ordered subring of
`ℝ` such as `ℚ`) with `2` invertible, and `B` a *positive definite* symmetric bilinear form, the
spin factor is formally real: a sum of squares can only vanish trivially. -/

section FormallyReal

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
theorem not_isFormallyReal_of_negVector (hB : B.IsSymm) {v : V} (hv : v ≠ 0)
    (_hneg : B v v < 0)
    (hsq : ∃ ι : Type, ∃ _ : Fintype ι, ∃ x : ι → R, -B v v = ∑ i, x i * x i) :
    ¬ @IsFormallyReal R (SpinFactor R V B) _ (jordanAlgebra B hB) := by
  rcases hsq with ⟨κ, hκ, x, hsq⟩
  letI : Fintype κ := hκ
  intro hFR
  letI : JordanAlgebra R (SpinFactor R V B) := jordanAlgebra B hB
  letI : IsFormallyReal R (SpinFactor R V B) := hFR
  let z : Option κ → SpinFactor R V B
    | none => mk B v 0
    | some i => mk B 0 (x i)
  have hsum : ∑ i, z i * z i = 0 := by
    ext
    · change fstLinear B (∑ i, z i * z i) = 0
      rw [map_sum]
      simp [z, Fintype.sum_option]
    · change sndLinear B (∑ i, z i * z i) = 0
      rw [map_sum]
      simp [z, Fintype.sum_option]
      rw [← hsq]
      ring
  have hzall : ∀ i : Option κ, z i = 0 :=
    IsFormallyReal.eq_zero_of_sum_mul_self_eq_zero
      (R := R) (M := SpinFactor R V B) (self := hFR) (ι := Option κ) z hsum
  have hz : z (none : Option κ) = 0 := hzall none
  exact hv (by simpa [z] using congrArg Prod.fst hz)

theorem not_isFormallyReal_int_of_negVector {V : Type*} [AddCommGroup V] [Module ℤ V]
    (B : LinearMap.BilinForm ℤ V) (hB : B.IsSymm) {v : V} (hv : v ≠ 0)
    (hneg : B v v < 0) :
    ¬ @IsFormallyReal ℤ (SpinFactor ℤ V B) _ (jordanAlgebra B hB) := by
  have hnonneg : 0 ≤ -B v v := le_of_lt (neg_pos.mpr hneg)
  obtain ⟨a, b, c, d, h4⟩ := Nat.sum_four_squares (Int.toNat (-B v v))
  apply not_isFormallyReal_of_negVector B hB hv hneg
  refine ⟨Fin 4, inferInstance,
    fun i => match i with
      | ⟨0, _⟩ => (a : ℤ)
      | ⟨1, _⟩ => (b : ℤ)
      | ⟨2, _⟩ => (c : ℤ)
      | ⟨3, _⟩ => (d : ℤ), ?_⟩
  rw [← Int.toNat_of_nonneg hnonneg, ← h4]
  norm_num [Fin.sum_univ_four]
  ring

theorem isFormallyRealPos (hB : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) :
    @IsFormallyReal R (SpinFactor R V B) _ (jordanAlgebra B hB) := by
  letI := jordanAlgebra B hB
  refine ⟨fun {ι} _ z hz i => ?_⟩
  have hsnd : ∑ j, (z j * z j).2 = 0 := by
    have h := congrArg (sndLinear B) hz
    simpa using h
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (z j * z j).2 := by
    intro j _
    have h1 : 0 ≤ B.toQuadraticMap (z j).1 := hPos.nonneg _
    have h2 : 0 ≤ (z j).2 * (z j).2 := mul_self_nonneg _
    simpa using add_nonneg h1 h2
  have heach : (z i * z i).2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsnd i (Finset.mem_univ i)
  have h1 : 0 ≤ B.toQuadraticMap (z i).1 := hPos.nonneg _
  have h2 : 0 ≤ (z i).2 * (z i).2 := mul_self_nonneg _
  have heach' : B.toQuadraticMap (z i).1 + (z i).2 * (z i).2 = 0 := by
    simpa using heach
  have hQ0 : B.toQuadraticMap (z i).1 = 0 := le_antisymm (by linarith) h1
  have ha0 : (z i).2 * (z i).2 = 0 := le_antisymm (by linarith) h2
  have hx0 : (z i).1 = 0 := by
    by_contra hxne
    exact absurd hQ0 (ne_of_gt (hPos _ hxne))
  have ha0' : (z i).2 = 0 := mul_self_eq_zero.mp ha0
  ext <;> simp [hx0, ha0']

end FormallyReal

section DetTrace

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The spin factor (under positivity, so it's formally real) has a generic trace and determinant
of rank `2`: the linear trace `τ(z) = 2 * z.2` and the determinant `Δ` from `determinant`, exactly
as for the classical rank-`2` Jordan algebras (e.g. `2 x 2` symmetric matrices). -/
noncomputable def detTrace (hB : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) :
    @IsFormallyRealDetTrace R (SpinFactor R V B) _ (jordanAlgebra B hB)
      (isFormallyRealPos B hB hPos) := by
  letI := jordanAlgebra B hB
  letI := isFormallyRealPos B hB hPos
  exact
    { rank := 2
      trace := (2 : R) • sndLinear B
      det := determinant B
      det_smul := fun r z => by
        have h := (determinant B).map_smul r z
        simpa [sq, pow_two] using h
      trace_one := by simp
      det_one := by simp }

end DetTrace

end SpinFactor
