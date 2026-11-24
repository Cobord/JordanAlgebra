module

public import Jordan

/-!
# Solution: proofs of the statements in `JordanCheck/Challenge.lean`

Each theorem restates the corresponding one in `JordanCheck/Challenge.lean` verbatim and proves it
from the `Jordan` library. `lake comparator` checks that the statements agree and that only
`propext`, `Quot.sound`, `Classical.choice` are used.
-/

@[expose] public section

universe u v

open JordanAlgebra

namespace JordanCheck

section General

variable {R : Type u} [CommRing R] {M : Type v} [JordanAlgebra R M]

attribute [local instance] LieRing.ofAssociativeRing in
theorem linearized_jordan_identity [Invertible (2 : R)] (a b c y : M) :
    a * ((b * c) * y) - (b * c) * (a * y) + (b * ((c * a) * y) - (c * a) * (b * y)) +
      (c * ((a * b) * y) - (a * b) * (c * y)) = 0 := by
  have h := congrArg (fun f : AddMonoid.End M => f y)
    (lie_lmul_lmul_add_add_eq_zero (R := R) a b c)
  simp only [Ring.lie_def] at h
  exact h

theorem linearized_fundamental_formula [Invertible (2 : R)] (b c d y : M) :
    ((b * d) * c) * y =
      (b * d) * (c * y) + (c * d) * (b * y) + (b * c) * (d * y)
        - b * (c * (d * y)) - d * (c * (b * y)) :=
  congrArg (fun f : AddMonoid.End M => f y) (lmul_mul_mul_eq (R := R) b c d)

theorem powers_operator_commute [Invertible (2 : R)] (x y : M) (m n : ℕ) :
    jordanPow x m * (jordanPow x n * y) = jordanPow x n * (jordanPow x m * y) :=
  jordanPow_mn (R := R) x y m n

theorem inner_derivation [Invertible (2 : R)] (x y a b : M) :
    x * (y * (a * b)) - y * (x * (a * b)) =
      a * (x * (y * b) - y * (x * b)) + (x * (y * a) - y * (x * a)) * b :=
  (JordanDerivation.inner (R := R) x y).leibniz a b

theorem formallyReal_scalars [IsFormallyReal R M] [Nontrivial M] :
    IsSemireal R ∧ CharZero R :=
  ⟨IsFormallyReal.neg_one_not_sum_squares (R := R) (M := M),
    IsFormallyReal.charZero_of_nontrivial_scalar (R := R) (M := M)⟩

end General

section SpinFactor

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

theorem spinFactor_jordan (B : LinearMap.BilinForm R V) (hB : B.IsSymm)
    (z w : SpinFactor R V B) :
    z * w = w * z ∧ z * z * (z * w) = z * (z * z * w) :=
  ⟨SpinFactor.spinFactor_mul_comm B hB z w,
    @JordanAlgebra.jordan_identity R _ _ (SpinFactor.jordanAlgebra B hB) z w⟩

theorem spinFactor_formallyReal [LinearOrder R] [IsStrictOrderedRing R]
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) :
    @IsFormallyReal R (SpinFactor R V B) _ (SpinFactor.jordanAlgebra B hB) :=
  SpinFactor.isFormallyRealPos B hB hPos

end SpinFactor

section Hermitian

variable (R : Type u) [CommRing R] [StarRing R] [TrivialStar R] [Invertible (2 : R)]
  [LinearOrder R] [IsStrictOrderedRing R] (n : Type v) [Fintype n] [DecidableEq n]

theorem symmetric_formallyReal : IsFormallyReal R (RealQM.symmetricMatrices R n) :=
  RealQM.isFormallyReal (R := R) (n := n)

theorem complexHermitian_formallyReal (a b : R) (hab : 4 * a + b * b < 0) :
    IsFormallyReal R (ComplexQM.hermitianMatrices R a b n) :=
  ComplexQM.isFormallyReal (R := R) (a := a) (b := b) (n := n) hab

theorem quaternionicHermitian_formallyReal (c₁ c₃ : R) (hc₁ : c₁ < 0) (hc₃ : c₃ < 0) :
    IsFormallyReal R (QuaternionicQM.hermitianMatrices R n c₁ 0 c₃) :=
  QuaternionicQM.isFormallyReal (R := R) (n := n) (c₁ := c₁) (c₃ := c₃) hc₁ hc₃

end Hermitian

theorem hermitian_three_jordan_identity {D : Type u} [NonUnitalNonAssocRing D] [IsAlternative D]
    [StarRing D] [IsNuclearInvolution D] (A B : Matrix (Fin 3) (Fin 3) D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A) = 0 :=
  hermitian_jordan_identity A B hA hB

section Octonion

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {a b c : R}

theorem octonion_alternative (x y : Octonion R a b c) :
    x * (x * y) = (x * x) * y ∧ (y * x) * x = y * (x * x) :=
  ⟨Octonion.alternative_left x y, Octonion.alternative_right x y⟩

variable [Invertible (2 : R)]

set_option maxHeartbeats 1000000 in
theorem albert_jordan (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0)
    (hc : ∀ x : R, c * x = 0 → x = 0)
    (x y : Octonion.AlbertAlgebra (R := R) (a := a) (b := b) (c := c)) :
    x * y = y * x ∧ x * x * (x * y) = x * (x * x * y) :=
  ⟨@JordanAlgebra.jordan_mul_comm R _ _ (Octonion.ofAlbert ha hb hc) x y,
    @JordanAlgebra.jordan_identity R _ _ (Octonion.ofAlbert ha hb hc) x y⟩

theorem albert_formallyReal [LinearOrder R] [IsStrictOrderedRing R] [NeZero a] [NeZero b]
    [NeZero c] (ha : a < 0) (hb : b < 0) (hc : 0 < c) :
    IsFormallyReal R (Octonion.AlbertAlgebra (R := R) (a := a) (b := b) (c := c)) :=
  Octonion.isFormallyReal_of_signs ha hb hc

end Octonion

end JordanCheck
