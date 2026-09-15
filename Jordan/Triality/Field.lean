import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Jordan.Triality.Basic

/-!
# Fields with involution as trialities

The simplest trialities live on a single field extension. In `Triality` only the base ring carries
a `star`; the modules do not. Accordingly, for a finite separable extension `K / F` of a field
with involution `F`, all that is needed on `K` is a ring automorphism `τ` compatible with `star`
on `F` (`τ (algebraMap r) = algebraMap (star r)`), and then

  `t x y z := Tr_{K/F} (x * τ y * z)`

is a `Triality F K K K` (`Triality.ofTrace`). `τ` need not be an involution. The `bij_*` axioms
come from multiplication by a nonzero field element being bijective, `τ` being bijective, and the
trace form being a perfect pairing `K ≃ Kᵛ` (`traceForm_nondegenerate`, which is where separability
enters).

Instances:

* `K = F`, `τ = star`: `t x y z = x * star y * z` for any field with involution
  (`Triality.ofTrace_self_apply`).
* Finite fields, `Triality.finiteFieldTriality`: base `Fq2 = 𝔽_{q²}` with the `q`-Frobenius
  involution `star r = r ^ q` over `Fq = 𝔽_q` (produced by `frobeniusStarRing`), and module `Fqn`
  any finite extension of `Fq2`, with `τ` the `q`-Frobenius `y ↦ y ^ q` of `Fqn`. Separability is
  automatic (finite fields are perfect).
-/

open LinearMap (BilinForm)

namespace Triality

section OfTrace

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

section TraceDual

variable [FiniteDimensional F K] [Algebra.IsSeparable F K]

/-- The trace form as a perfect pairing `K ≃ Kᵛ`, `w ↦ Tr (w * ·)`. -/
noncomputable def traceDual : K ≃ₗ[F] Module.Dual F K :=
  (Algebra.traceForm F K).toDual (traceForm_nondegenerate F K)

@[simp] theorem traceDual_apply (w z : K) : traceDual F K w z = Algebra.trace F K (w * z) :=
  BilinForm.toDual_def _

end TraceDual

variable [StarRing F] (τ : K ≃+* K) (hτ : ∀ r : F, τ (algebraMap F K r) = algebraMap F K (star r))
include hτ

/-- A `star`-compatible automorphism of `K` is `starRingEnd F`-semilinear. -/
theorem conj_smul (r : F) (y : K) : τ (r • y) = star r • τ y := by
  rw [Algebra.smul_def, map_mul, hτ, ← Algebra.smul_def]

theorem conj_symm_smul (r : F) (y : K) : τ.symm (r • y) = star r • τ.symm y :=
  τ.symm_apply_eq.mpr (by rw [conj_smul F K τ hτ, star_star, τ.apply_symm_apply])

/-- The trilinear form `t x y z = Tr_{K/F} (x * τ y * z)`, antilinear in `y`. -/
noncomputable def traceForm₃ : K →ₗ[F] K →ₛₗ[starRingEnd F] Module.Dual F K :=
  LinearMap.mk₂'ₛₗ (RingHom.id F) (starRingEnd F) (fun x y => Algebra.traceForm F K (x * τ y))
    (fun x x' y => by rw [add_mul, map_add])
    (fun r x y => by rw [smul_mul_assoc, map_smul]; rfl)
    (fun x y y' => by rw [map_add, mul_add, map_add])
    (fun r x y => by rw [conj_smul F K τ hτ, mul_smul_comm, map_smul, starRingEnd_apply])

@[simp] theorem traceForm₃_apply (x y z : K) :
    traceForm₃ F K τ hτ x y z = Algebra.trace F K (x * τ y * z) := rfl

/-- Precomposition with `τ` turns linear functionals into `starRingEnd F`-semilinear ones. -/
def conjPrecomp : Module.Dual F K ≃ (K →ₛₗ[starRingEnd F] F) where
  toFun f :=
    { toFun := fun y => f (τ y)
      map_add' := fun y y' => by rw [map_add, map_add]
      map_smul' := fun r y => by rw [conj_smul F K τ hτ, map_smul, starRingEnd_apply] }
  invFun g :=
    { toFun := fun y => g (τ.symm y)
      map_add' := fun y y' => by rw [map_add, map_add]
      map_smul' := fun r y => by
        rw [conj_symm_smul F K τ hτ, map_smulₛₗ, starRingEnd_apply, star_star]; rfl }
  left_inv f := LinearMap.ext fun y => by simp
  right_inv g := LinearMap.ext fun y => by simp

variable [FiniteDimensional F K] [Algebra.IsSeparable F K]

/-- The conjugate-dual pairing `K ≃ (K →ₛₗ[starRingEnd F] F)`, `w ↦ Tr (w * τ ·)`. -/
noncomputable def traceConjDual : K ≃ (K →ₛₗ[starRingEnd F] F) :=
  (traceDual F K).toEquiv.trans (conjPrecomp F K τ hτ)

@[simp] theorem traceConjDual_apply (w y : K) :
    traceConjDual F K τ hτ w y = Algebra.trace F K (w * τ y) := rfl

/-- `Tr_{K/F} (x * τ y * z)` is a triality on `K` over `F`. Each `bij_*` axiom is one of the two
dual pairings composed with multiplication by a nonzero element (and `τ`). -/
noncomputable abbrev ofTrace : Triality F K K K where
  triality_prod := traceForm₃ F K τ hτ
  nontrivial_x := inferInstance
  nontrivial_y := inferInstance
  nontrivial_z := inferInstance
  -- `y ↦ Tr (x (τ y) ·) = traceDual (x * τ y)`
  bij_x_yz x hx := by
    have : ⇑(traceForm₃ F K τ hτ x) = ⇑(traceDual F K) ∘ (x * ·) ∘ τ := by
      funext y; ext z
      simp only [traceForm₃_apply, Function.comp_apply, traceDual_apply]
    rw [this]
    exact (traceDual F K).bijective.comp ((Equiv.mulLeft₀ x hx).bijective.comp τ.bijective)
  -- `z ↦ Tr (x (τ ·) z) = traceConjDual (x z)`
  bij_x_zy x hx := by
    have : ⇑(traceForm₃ F K τ hτ x).flip = ⇑(traceConjDual F K τ hτ) ∘ (x * ·) := by
      funext z; ext y
      simp only [LinearMap.flip_apply, traceForm₃_apply, Function.comp_apply,
        traceConjDual_apply, mul_right_comm]
    rw [this]
    exact (traceConjDual F K τ hτ).bijective.comp (Equiv.mulLeft₀ x hx).bijective
  -- `x ↦ Tr (x (τ y) ·) = traceDual (x * τ y)`
  bij_y_xz y hy := by
    have : ⇑((traceForm₃ F K τ hτ).flip y) = ⇑(traceDual F K) ∘ (· * τ y) := by
      funext x; ext z
      simp only [LinearMap.flip_apply, traceForm₃_apply, Function.comp_apply, traceDual_apply]
    rw [this]
    exact (traceDual F K).bijective.comp
      (Equiv.mulRight₀ (τ y) (τ.map_ne_zero_iff.mpr hy)).bijective
  -- `z ↦ Tr (· (τ y) z) = traceDual (τ y * z)`
  bij_y_zx y hy := by
    have : ⇑((traceForm₃ F K τ hτ).flip y).flip = ⇑(traceDual F K) ∘ (τ y * ·) := by
      funext z; ext x
      simp only [LinearMap.flip_apply, traceForm₃_apply, Function.comp_apply, traceDual_apply]
      ring_nf
    rw [this]
    exact (traceDual F K).bijective.comp
      (Equiv.mulLeft₀ (τ y) (τ.map_ne_zero_iff.mpr hy)).bijective
  -- `x ↦ Tr (x (τ ·) z) = traceConjDual (x z)`
  bij_z_xy z hz := by
    have : (fun x => (traceForm₃ F K τ hτ x).flip z) = ⇑(traceConjDual F K τ hτ) ∘ (· * z) := by
      funext x; ext y
      simp only [LinearMap.flip_apply, traceForm₃_apply, Function.comp_apply,
        traceConjDual_apply, mul_right_comm]
    rw [this]
    exact (traceConjDual F K τ hτ).bijective.comp (Equiv.mulRight₀ z hz).bijective
  -- `y ↦ Tr (· (τ y) z) = traceDual (τ y * z)`
  bij_z_yx z hz := by
    have : (fun y => ((traceForm₃ F K τ hτ).flip y).flip z) =
        ⇑(traceDual F K) ∘ (· * z) ∘ τ := by
      funext y; ext x
      simp only [LinearMap.flip_apply, traceForm₃_apply, Function.comp_apply, traceDual_apply]
      ring_nf
    rw [this]
    exact (traceDual F K).bijective.comp ((Equiv.mulRight₀ z hz).bijective.comp τ.bijective)

@[simp] theorem ofTrace_triality_prod (x y z : K) :
    (ofTrace F K τ hτ).triality_prod x y z = Algebra.trace F K (x * τ y * z) := rfl

end OfTrace

section Self

variable (F : Type*) [Field F] [StarRing F]

/-- On `K = F` with `τ = star`, the trace is the identity: `t x y z = x * star y * z`. -/
theorem ofTrace_self_apply (x y z : F) :
    (ofTrace F F starRingAut (fun _ => rfl)).triality_prod x y z = x * star y * z := by
  rw [ofTrace_triality_prod, Algebra.trace_self_apply]; rfl

end Self

section FiniteField

/-! ### Finite fields with the Frobenius involution

The tower is `Fq ⊆ Fq2 ⊆ Fqn`, with `q = #Fq`:

* `Fq2 = 𝔽_{q²}` is the base field with involution `star r = r ^ q`, the `q`-Frobenius over `Fq`
  (`frobeniusStarRing`); its fixed field is `Fq`.
* `Fqn` is any finite extension of `Fq2` — the module of the triality, of arbitrary degree over
  the base. The `q`-Frobenius `y ↦ y ^ q` of `Fqn` restricts to `star` on `Fq2`, so it is the
  `star`-compatible automorphism `τ` that `ofTrace` needs; `Fqn` itself carries no `star`.

Only the exponent `q = #Fq` and the two Frobenius maps are used: no compatibility between the
`Fq`-algebra structures of `Fq2` and `Fqn` (an `IsScalarTower`) has to be assumed. -/

/-- A `StarRing` structure on a commutative ring from an involutive ring endomorphism. -/
abbrev starRingOfInvolutive {A : Type*} [CommRing A] (σ : A →+* A) (hσ : Function.Involutive σ) :
    StarRing A where
  star := σ
  star_involutive := hσ
  star_mul x y := by simp only [map_mul, mul_comm]
  star_add := map_add σ

section BaseInvolution

variable (Fq Fq2 : Type*) [Field Fq] [Fintype Fq] [Field Fq2] [Fintype Fq2] [Algebra Fq Fq2]

/-- On `Fq2 = 𝔽_{q²}` the `q`-Frobenius `r ↦ r ^ q` is an involution. -/
theorem frobenius_involutive (h : Fintype.card Fq2 = Fintype.card Fq ^ 2) :
    Function.Involutive (FiniteField.frobeniusAlgHom Fq Fq2) := fun r => by
  simp only [FiniteField.coe_frobeniusAlgHom]
  rw [← pow_mul, ← sq, ← h, FiniteField.pow_card]

/-- The `q`-Frobenius involution `r ↦ r ^ q` as a `StarRing` structure on `Fq2 = 𝔽_{q²}`. -/
abbrev frobeniusStarRing (h : Fintype.card Fq2 = Fintype.card Fq ^ 2) : StarRing Fq2 :=
  starRingOfInvolutive (FiniteField.frobeniusAlgHom Fq Fq2).toRingHom (frobenius_involutive Fq Fq2 h)

theorem frobeniusStarRing_star (h : Fintype.card Fq2 = Fintype.card Fq ^ 2) (r : Fq2) :
    letI := frobeniusStarRing Fq Fq2 h
    star r = r ^ Fintype.card Fq :=
  rfl

end BaseInvolution

section Extension

variable (Fq Fq2 Fqn : Type*) [Field Fq] [Fintype Fq] [Field Fq2] [Fintype Fq2] [StarRing Fq2]
  [Field Fqn] [Fintype Fqn] [Algebra Fq Fqn] [Algebra Fq2 Fqn]

/-- The `q`-Frobenius `y ↦ y ^ q` as a ring automorphism of `Fqn`. -/
noncomputable def frobeniusEquiv : Fqn ≃+* Fqn :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic Fq Fqn).toRingEquiv

@[simp] theorem frobeniusEquiv_apply (y : Fqn) : frobeniusEquiv Fq Fqn y = y ^ Fintype.card Fq :=
  rfl

/-- `Fqn` over `Fq2 = 𝔽_{q²}` with `star r = r ^ q` (e.g. `frobeniusStarRing`): the `q`-Frobenius of
`Fqn` is `star`-compatible, giving `t x y z = Tr_{Fqn/Fq2} (x * y ^ q * z)`, in every degree of
`Fqn` over `Fq2`. -/
noncomputable abbrev finiteFieldTriality (hstar : ∀ r : Fq2, star r = r ^ Fintype.card Fq) :
    Triality Fq2 Fqn Fqn Fqn :=
  ofTrace Fq2 Fqn (frobeniusEquiv Fq Fqn) fun r => by rw [frobeniusEquiv_apply, hstar, map_pow]

@[simp] theorem finiteFieldTriality_triality_prod (hstar : ∀ r : Fq2, star r = r ^ Fintype.card Fq)
    (x y z : Fqn) :
    (finiteFieldTriality Fq Fq2 Fqn hstar).triality_prod x y z =
      Algebra.trace Fq2 Fqn (x * y ^ Fintype.card Fq * z) := rfl

end Extension

end FiniteField

end Triality
