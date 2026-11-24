module

public import Jordan.SpinFactor
public import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# Formal reality of spin factors

* `SpinFactor.isFormallyRealPos` (in `Jordan/SpinFactor.lean`): over a totally ordered ring, the
  spin factor of a symmetric form with `B(v, v) > 0` for every `v ≠ 0` is formally real.
* `SpinFactor.isFormallyReal_iff_posDef`: **over a real closed field the converse holds**, so
  `J(V, B)` is formally real exactly when `B` is positive definite. If `B(v, v) ≤ 0` with `v ≠ 0`,
  write `-B(v, v) = s²`; then `v² + (s 1)² = (B(v, v) + s²) 1 = 0` with `v ≠ 0`.
-/

@[expose] public section

namespace SpinFactor

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  [AddCommGroup V] [Module R V] (B : LinearMap.BilinForm R V)

/-- **Formal reality of spin factors over a real closed field**: `J(V, B)` is formally real if
and only if `B` is positive definite. -/
theorem isFormallyReal_iff_posDef (hB : B.IsSymm) :
    @IsFormallyReal R (SpinFactor R V B) _ (jordanAlgebra B hB) ↔ B.toQuadraticMap.PosDef := by
  let _ := jordanAlgebra B hB
  refine ⟨fun hFR v hv => ?_, fun hPos => isFormallyRealPos B hB hPos⟩
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare (x := -(B v v))).1
    (neg_nonneg.2 (by simpa using hle))
  let x : Fin 2 → SpinFactor R V B := ![mk B v 0, mk B 0 s]
  have hsum : ∑ i, x i * x i = 0 := by
    rw [Fin.sum_univ_two]
    ext
    · simp [x]
    · simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, add_snd, mul_snd, mk_fst, mk_snd,
        map_zero, mul_zero, add_zero, zero_add, zero_snd]
      rw [← hs]
      ring
  have := hFR.eq_zero_of_sum_mul_self_eq_zero x hsum 0
  exact hv (congrArg Prod.fst this)

end SpinFactor
