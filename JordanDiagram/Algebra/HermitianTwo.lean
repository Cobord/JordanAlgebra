module

public import Jordan.OctonionMatrix
public import JordanDiagram.Algebra.OctonionNorm

/-!
# Two-by-two Hermitian matrices over the Cayley–Dickson stages are spin factors

`Octonion.ofSymmetricMatricesTwo` (in `Jordan/OctonionMatrix.lean`) sends a Hermitian matrix
`!![ρ + α, x; x̄, ρ - α]` over `C₃ = Octonion R a b c` to `((x, α), ρ)` in the spin factor of
`hermitianTwoBilin ((x, α), (y, β)) = n(x, y) + αβ`, with `n` the polar form of the norm, for all
parameters (zero divisors included). Here:

* `Octonion.ofSymmetricMatricesTwo_smul`, `Octonion.hermitianTwoLinearEquiv`: the map is
  `R`-linear, so it is an isomorphism of Jordan algebras.
* `Octonion.cdStage k`: the Cayley–Dickson stages `C₀ = R ⊆ C₁ ⊆ C₂ ⊆ C₃`, spanned by the first
  `2ᵏ` standard basis vectors; each is closed under the product and the conjugation and contains `1`
  (`one_mem_cdStage`, `mul_mem_cdStage`, `star_mem_cdStage`).
* `Octonion.forall_mem_cdStage_iff`: **compatibility with the stages**: a Hermitian matrix has all
  its entries in `Cₖ` exactly when the vector part of its image lies in `Cₖ`, so the isomorphism
  restricts to `H₂(Cₖ) ≅ J(Cₖ ⊕ R)` for every `k`.
* With `Octonion.innerProduct_eq_sum`, `n` is diagonal with the norm coefficients, and on `Cₖ` only
  the first `2ᵏ` of them occur (`innerProduct_eq_sum_of_mem_cdStage`).
-/

@[expose] public section

open scoped Quaternion

namespace Octonion

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R] {a b c : R}

/-! ### Linearity -/

theorem ofSymmetricMatricesTwo_apply
    (M : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2)) :
    ofSymmetricMatricesTwo M = SpinFactor.mk _ (M.val 0 1, HermitianOctonionMatrixTwo.diffHalf M)
      (HermitianOctonionMatrixTwo.traceHalf M) := rfl

theorem ofSymmetricMatricesTwo_smul (r : R)
    (M : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2)) :
    ofSymmetricMatricesTwo (r • M) = r • ofSymmetricMatricesTwo M := by
  apply SpinFactor.ext
  · apply Prod.ext
    · rfl
    · change ⅟(2 : R) * (r * (M.val 0 0).1.re - r * (M.val 1 1).1.re) =
        r * (⅟(2 : R) * ((M.val 0 0).1.re - (M.val 1 1).1.re))
      ring
  · change ⅟(2 : R) * (r * (M.val 0 0).1.re + r * (M.val 1 1).1.re) =
      r * (⅟(2 : R) * ((M.val 0 0).1.re + (M.val 1 1).1.re))
    ring

/-- `H₂(C₃) ≅ J(C₃ ⊕ R)` as an `R`-linear isomorphism; it is multiplicative
(`hermitianTwoLinearEquiv_mul`). -/
noncomputable def hermitianTwoLinearEquiv :
    HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2) ≃ₗ[R]
      SpinFactor R (Octonion R a b c × R) (hermitianTwoBilin (R := R) (a := a) (b := b) (c := c)) :=
  { ofSymmetricMatricesTwo.toAddEquiv with
    map_smul' := ofSymmetricMatricesTwo_smul }

theorem hermitianTwoLinearEquiv_mul
    (M N : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2)) :
    hermitianTwoLinearEquiv (M * N) = hermitianTwoLinearEquiv M * hermitianTwoLinearEquiv N :=
  map_mul ofSymmetricMatricesTwo M N

theorem hermitianTwoBilin_apply (x y : Octonion R a b c) (α β : R) :
    hermitianTwoBilin (x, α) (y, β) = innerProduct x y + α * β := rfl

end Octonion

/-! ### The Cayley–Dickson stages -/

namespace Octonion

variable {R : Type*} [CommRing R] {a b c : R}

/-- The Cayley–Dickson stage `Cₖ ⊆ C₃`, spanned by the first `2ᵏ` standard basis vectors
`1, i, j, k, ℓ, iℓ, jℓ, kℓ`: `C₀ = R`, `C₁ = R ⊕ R i`, `C₂` the quaternions, `C₃` everything. -/
def cdStage (k : ℕ) : Submodule R (Octonion R a b c) where
  carrier := {x | ∀ i : Fin 8, 2 ^ k ≤ (i : ℕ) → coords x i = 0}
  add_mem' {x y} hx hy i hi := by
    rw [← coordsEquiv_apply, map_add, Pi.add_apply, coordsEquiv_apply, coordsEquiv_apply, hx i hi,
      hy i hi, add_zero]
  zero_mem' i _ := by
    rw [← coordsEquiv_apply, map_zero, Pi.zero_apply]
  smul_mem' r x hx i hi := by
    rw [← coordsEquiv_apply, map_smul, Pi.smul_apply, coordsEquiv_apply, hx i hi, smul_zero]

theorem mem_cdStage_zero_iff {x : Octonion R a b c} :
    x ∈ cdStage 0 ↔ x.1.imI = 0 ∧ x.1.imJ = 0 ∧ x.1.imK = 0 ∧ x.2 = 0 := by
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide),
      QuaternionAlgebra.ext (h 4 (by decide)) (h 5 (by decide)) (h 6 (by decide)) (h 7 (by decide))⟩
  · rintro ⟨h1, h2, h3, h4⟩ i hi
    fin_cases i <;> simp_all [coords]

theorem mem_cdStage_one_iff {x : Octonion R a b c} :
    x ∈ cdStage 1 ↔ x.1.imJ = 0 ∧ x.1.imK = 0 ∧ x.2 = 0 := by
  constructor
  · intro h
    exact ⟨h 2 (by decide), h 3 (by decide),
      QuaternionAlgebra.ext (h 4 (by decide)) (h 5 (by decide)) (h 6 (by decide)) (h 7 (by decide))⟩
  · rintro ⟨h2, h3, h4⟩ i hi
    fin_cases i <;> simp_all [coords]

theorem mem_cdStage_two_iff {x : Octonion R a b c} : x ∈ cdStage 2 ↔ x.2 = 0 := by
  constructor
  · intro h
    exact QuaternionAlgebra.ext (h 4 (by decide)) (h 5 (by decide)) (h 6 (by decide))
      (h 7 (by decide))
  · rintro h4 i hi
    fin_cases i <;> simp_all [coords]

theorem cdStage_eq_top {k : ℕ} (hk : 3 ≤ k) : cdStage k = (⊤ : Submodule R (Octonion R a b c)) := by
  refine eq_top_iff.2 fun x _ i hi => absurd hi (not_le.2 (lt_of_lt_of_le i.2 ?_))
  calc 8 = 2 ^ 3 := rfl
    _ ≤ 2 ^ k := Nat.pow_le_pow_right two_pos hk

theorem cdStage_cases (k : ℕ) : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega

section StarAspects

/- `[StarRing R] [TrivialStar R]` are opened up manifestly from the first lemma touching the
octonion product, unit or conjugation, following `Jordan/Octonion.lean` (see the comment opening
its `StarAspects` section). That `star`, and the Cayley–Dickson product built from it, is defined
purely from `R`'s ring operations and never looks at a `Star R` instance; the hypotheses are kept
visible, and not omitted where a lemma does not use them, so that the octonion's own `star` cannot
be silently confused with an `R`-level one (which is what `StarModule` and the Hermitian matrices
genuinely involve). Hence `set_option linter.unusedSectionVars false` on the lemmas below that do
not use them. -/
variable [StarRing R] [TrivialStar R]

set_option linter.unusedSectionVars false in
theorem one_mem_cdStage (k : ℕ) : (1 : Octonion R a b c) ∈ cdStage k := by
  rcases cdStage_cases k with rfl | rfl | rfl | hk
  · exact mem_cdStage_zero_iff.2 ⟨by simp, by simp, by simp, rfl⟩
  · exact mem_cdStage_one_iff.2 ⟨by simp, by simp, rfl⟩
  · exact mem_cdStage_two_iff.2 rfl
  · rw [cdStage_eq_top hk]
    trivial

set_option linter.unusedSectionVars false in
theorem star_mem_cdStage {k : ℕ} {x : Octonion R a b c} (hx : x ∈ cdStage k) :
    star x ∈ cdStage k := by
  rcases cdStage_cases k with rfl | rfl | rfl | hk
  · obtain ⟨h1, h2, h3, h4⟩ := mem_cdStage_zero_iff.1 hx
    exact mem_cdStage_zero_iff.2 ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4]⟩
  · obtain ⟨h2, h3, h4⟩ := mem_cdStage_one_iff.1 hx
    exact mem_cdStage_one_iff.2 ⟨by simp [h2], by simp [h3], by simp [h4]⟩
  · exact mem_cdStage_two_iff.2 (by simp [mem_cdStage_two_iff.1 hx])
  · rw [cdStage_eq_top hk]
    trivial

set_option linter.unusedSectionVars false in
theorem mul_mem_cdStage {k : ℕ} {x y : Octonion R a b c} (hx : x ∈ cdStage k)
    (hy : y ∈ cdStage k) : x * y ∈ cdStage k := by
  rcases cdStage_cases k with rfl | rfl | rfl | hk
  · obtain ⟨x1, x2, x3, x4⟩ := mem_cdStage_zero_iff.1 hx
    obtain ⟨y1, y2, y3, y4⟩ := mem_cdStage_zero_iff.1 hy
    refine mem_cdStage_zero_iff.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp [x1, x2, x3, x4, y1, y2, y3, y4]
  · obtain ⟨x2, x3, x4⟩ := mem_cdStage_one_iff.1 hx
    obtain ⟨y2, y3, y4⟩ := mem_cdStage_one_iff.1 hy
    refine mem_cdStage_one_iff.2 ⟨?_, ?_, ?_⟩ <;> simp [x2, x3, x4, y2, y3, y4]
  · exact mem_cdStage_two_iff.2 (by simp [mem_cdStage_two_iff.1 hx, mem_cdStage_two_iff.1 hy])
  · rw [cdStage_eq_top hk]
    trivial

theorem scalarEmbed_mem_cdStage [Invertible (2 : R)] (k : ℕ) (r : R) :
    (scalarEmbed r : Octonion R a b c) ∈ cdStage k := by
  rw [← mul_one (scalarEmbed r : Octonion R a b c), scalarEmbed_mul]
  exact (cdStage k).smul_mem r (one_mem_cdStage k)

/-- **Compatibility with the Cayley–Dickson stages**: a Hermitian `2 × 2` matrix has all its entries
in `Cₖ` exactly when the vector part of its image in the spin factor lies in `Cₖ`. -/
theorem forall_mem_cdStage_iff [Invertible (2 : R)] (k : ℕ)
    (M : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2)) :
    (∀ i j, M.val i j ∈ cdStage k) ↔ (ofSymmetricMatricesTwo M).1.1 ∈ cdStage k := by
  refine ⟨fun h => h 0 1, fun h i j => ?_⟩
  change M.val 0 1 ∈ cdStage k at h
  fin_cases i <;> fin_cases j
  · obtain ⟨r, hr⟩ := diag_real M 0
    exact hr ▸ scalarEmbed_mem_cdStage k r
  · exact h
  · exact (HermitianOctonionMatrixTwo.off_diag M).symm ▸ star_mem_cdStage h
  · obtain ⟨r, hr⟩ := diag_real M 1
    exact hr ▸ scalarEmbed_mem_cdStage k r

/-- On the stage `Cₖ`, the polar form of the norm only involves the first `2ᵏ` norm coefficients. -/
theorem innerProduct_eq_sum_of_mem_cdStage [Invertible (2 : R)] {k : ℕ}
    {x : Octonion R a b (-c)} (hx : x ∈ cdStage k) (y : Octonion R a b (-c)) :
    innerProduct x y =
      ∑ i : Fin 8, if (i : ℕ) < 2 ^ k then normCoeff a b c i * coords x i * coords y i else 0 := by
  rw [innerProduct_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [hx i (not_lt.1 h), mul_zero, zero_mul]

end StarAspects

end Octonion
