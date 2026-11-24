module

public import Jordan

/-!
# Challenge: trusted statements of the main results of `Jordan`

This file is the **trusted specification** checked by `lake comparator` (configured by
`comparator.json` at the project root). Every theorem here is stated with `sorry`;
`JordanCheck/Solution.lean` must prove exactly the same statements, using only the axioms
`propext`, `Quot.sound`, `Classical.choice`.

Wherever possible a result is stated in elementary terms, through the product of the algebra
in question, rather than through a library construction. For instance, that the spin factor and
the Albert algebra are Jordan algebras is stated as commutativity and the Jordan identity for
their concrete products, not as the existence of a `JordanAlgebra` instance.

Review this file, not `Solution.lean`: if these statements say what is intended, a passing
`lake comparator` run certifies the formalization of them.
-/

@[expose] public section

-- The `sorry`s below are the intended placeholders of the challenge; silence their warnings.
set_option warn.sorry false

universe u v

open JordanAlgebra

namespace JordanCheck

section General

variable {R : Type u} [CommRing R] {M : Type v} [JordanAlgebra R M]

/-- **Linearized Jordan identity**: with `2` invertible,
`[L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}] = 0`, evaluated at `y`. -/
theorem linearized_jordan_identity [Invertible (2 : R)] (a b c y : M) :
    a * ((b * c) * y) - (b * c) * (a * y) + (b * ((c * a) * y) - (c * a) * (b * y)) +
      (c * ((a * b) * y) - (a * b) * (c * y)) = 0 := by
  sorry

/-- **Linearized fundamental formula**: with `2` invertible,
`L_{(bd)c} = L_{bd} L_c + L_{cd} L_b + L_{bc} L_d - L_b L_c L_d - L_d L_c L_b`, evaluated at `y`. -/
theorem linearized_fundamental_formula [Invertible (2 : R)] (b c d y : M) :
    ((b * d) * c) * y =
      (b * d) * (c * y) + (c * d) * (b * y) + (b * c) * (d * y)
        - b * (c * (d * y)) - d * (c * (b * y)) := by
  sorry

/-- **Powers operator-commute**: with `2` invertible, multiplications by any two powers of the
same element commute. -/
theorem powers_operator_commute [Invertible (2 : R)] (x y : M) (m n : ℕ) :
    jordanPow x m * (jordanPow x n * y) = jordanPow x n * (jordanPow x m * y) := by
  sorry

/-- **Inner derivations**: with `2` invertible, `[L_x, L_y]` is a derivation. -/
theorem inner_derivation [Invertible (2 : R)] (x y a b : M) :
    x * (y * (a * b)) - y * (x * (a * b)) =
      a * (x * (y * b) - y * (x * b)) + (x * (y * a) - y * (x * a)) * b := by
  sorry

/-- **Jordan triple identity**: with `2` invertible, the triple product
`{x, y, z} = (x * y*) * z + (z * y*) * x - (x * z) * y*` of a Jordan algebra with involution
(antilinear in `y`) satisfies
`{x, y, {u, v, w}} - {u, v, {x, y, w}} = {{x, y, u}, v, w} - {u, {y, x, v}, w}`. -/
theorem jordan_triple_identity [Invertible (2 : R)] [StarRing R] [StarRing M] [StarModule R M]
    (x y u v w : M) :
    tripleProduct x y (tripleProduct u v w) - tripleProduct u v (tripleProduct x y w) =
      tripleProduct (tripleProduct x y u) v w - tripleProduct u (tripleProduct y x v) w := by
  sorry

/-- **Scalars of a formally real Jordan algebra**: if a nontrivial Jordan `R`-algebra is formally
real, then `-1` is not a sum of squares in `R`, and `R` has characteristic zero. -/
theorem formallyReal_scalars [IsFormallyReal R M] [Nontrivial M] :
    IsSemireal R ∧ CharZero R := by
  sorry

end General

section SpinFactor

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- **Spin factors are Jordan**: for any symmetric bilinear form `B`, the product
`(x, a) ∘ (y, b) = (a • y + b • x, B x y + a * b)` on `V × R` is commutative and satisfies the
Jordan identity. -/
theorem spinFactor_jordan (B : LinearMap.BilinForm R V) (hB : B.IsSymm)
    (z w : SpinFactor R V B) :
    z * w = w * z ∧ z * z * (z * w) = z * (z * z * w) := by
  sorry

/-- **Spin factors of positive definite forms are formally real**, for their Jordan algebra
structure `SpinFactor.jordanAlgebra`. -/
theorem spinFactor_formallyReal [LinearOrder R] [IsStrictOrderedRing R]
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) :
    @IsFormallyReal R (SpinFactor R V B) _ (SpinFactor.jordanAlgebra B hB) := by
  sorry

end SpinFactor

section Hermitian

variable (R : Type u) [CommRing R] [StarRing R] [TrivialStar R] [Invertible (2 : R)]
  [LinearOrder R] [IsStrictOrderedRing R] (n : Type v) [Fintype n] [DecidableEq n]

/-- **Symmetric matrices are formally real** over an ordered ring. -/
theorem symmetric_formallyReal : IsFormallyReal R (RealQM.symmetricMatrices R n) := by
  sorry

/-- **Hermitian matrices over a quadratic algebra are formally real** when its norm form is
definite (`4a + b² < 0`). -/
theorem complexHermitian_formallyReal (a b : R) (hab : 4 * a + b * b < 0) :
    IsFormallyReal R (ComplexQM.hermitianMatrices R a b n) := by
  sorry

/-- **Hermitian matrices over a quaternion algebra are formally real** when its norm form is
definite (`c₁ < 0`, `c₃ < 0`). -/
theorem quaternionicHermitian_formallyReal (c₁ c₃ : R) (hc₁ : c₁ < 0) (hc₃ : c₃ < 0) :
    IsFormallyReal R (QuaternionicQM.hermitianMatrices R n c₁ 0 c₃) := by
  sorry

end Hermitian

/-- **Jordan identity for `3 × 3` Hermitian matrices**, over any alternative ring with nuclear
involution, in the undivided form `[A ∘ B, A²] = 0` with `X ∘ Y = XY + YX`. -/
theorem hermitian_three_jordan_identity {D : Type u} [NonUnitalNonAssocRing D] [IsAlternative D]
    [StarRing D] [IsNuclearInvolution D] (A B : Matrix (Fin 3) (Fin 3) D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B + B * A) * (A * A) + (A * A) * (A * B + B * A)
      - (A * (B * (A * A) + (A * A) * B) + (B * (A * A) + (A * A) * B) * A) = 0 := by
  sorry

section Octonion

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {a b c : R}

/-- **Octonions are alternative**: the Cayley–Dickson double of a quaternion algebra satisfies
both alternative laws. -/
theorem octonion_alternative (x y : Octonion R a b c) :
    x * (x * y) = (x * x) * y ∧ (y * x) * x = y * (x * x) := by
  sorry

variable [Invertible (2 : R)]

/-- **The Albert algebra is Jordan**: when `a`, `b`, `c` are non-zero-divisors, the product
`X ∘ Y = ½(XY + YX)` on `3 × 3` Hermitian octonionic matrices is commutative and satisfies the
Jordan identity. -/
theorem albert_jordan (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0)
    (hc : ∀ x : R, c * x = 0 → x = 0)
    (x y : Octonion.AlbertAlgebra (R := R) (a := a) (b := b) (c := c)) :
    x * y = y * x ∧ x * x * (x * y) = x * (x * x * y) := by
  sorry

/-- **The Albert algebra is formally real** over an ordered ring when `a < 0`, `b < 0`, `0 < c`
(the octonions with definite norm). Its Jordan algebra structure is the instance available when
`a`, `b`, `c` are nonzero in a ring without zero divisors. -/
theorem albert_formallyReal [LinearOrder R] [IsStrictOrderedRing R] [NeZero a] [NeZero b]
    [NeZero c] (ha : a < 0) (hb : b < 0) (hc : 0 < c) :
    IsFormallyReal R (Octonion.AlbertAlgebra (R := R) (a := a) (b := b) (c := c)) := by
  sorry

end Octonion

end JordanCheck
