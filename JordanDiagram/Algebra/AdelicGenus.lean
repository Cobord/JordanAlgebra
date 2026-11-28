module

public import JordanDiagram.MathlibMissing.ClassSum
public import JordanDiagram.Algebra.DyadicFinite
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# The adelic genus of a chain over `Z[1/2]`

Let `E` be a `ℚ`-vector space with a symmetric bilinear form `B`, and let a chain be given by
families `bᵢ` of vectors of `E`, each linearly independent over `ℚ`. Its members are the
`Z[1/2]`-spans `Lᵢ` of the `bᵢ` (`member`), inside the `ℚ`-spans `Wᵢ` (`memberSpan`). Here `Z[1/2]` is
`dyadic`, the rationals integral at every prime other than `2`.

Over the finite adeles `𝔸_f` of `ℚ`:
* the members span `𝔸_f`-modules `𝔸_f Wᵢ` (`adelicSpan`) and modules `Ô' Lᵢ` (`adelicMember`)
  over the adeles integral at every odd prime (`dyadicAdeles`);
* the group `G(𝔸_f)` (`adelicGroup`) consists of the isometries of `𝔸_f ⊗ E` preserving every
  `𝔸_f Wᵢ`;
* it contains the rational points `Γ = G(ℚ)` (`ratImage`), the isometries of `E` preserving every
  `Wᵢ`, by base change (`baseChangeHom`);
* it contains the level `K` (`adelicLevel`), the stabilizer of every `Ô' Lᵢ`.

The genus is the double coset space `Γ \ G(𝔸_f) / K` (`genus`), and its mass is the class sum of
`1` (`genusMass`). At the prime `2` the level imposes no condition. An adelic element `g`, as data,
picks out a class.

`card_classAut_one`: the stabilizer `Γ ∩ K` of the class of `1` is the automorphism group of the
chain, the isometries of `E` preserving every member (`chainAut`). The proof rests on
`mem_member_of_toAf_mem`: a vector of `Wᵢ` whose image lies in `Ô' Lᵢ` lies in `Lᵢ`, because the
rationals integral at every odd prime are `dyadic` (`algebraMap_mem_dyadicAdeles`).

## Sources

* The description of the classes in a genus as `G(ℚ) \ G(𝔸_f) / K`, and of the mass as
  `∑ 1/#(Γ ∩ gKg⁻¹)`: V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic
  Press, 1994, chapter 8; J. W. S. Cassels, *Rational Quadratic Forms*, Academic Press, 1978.
* The same set-up for hermitian lattices over a CM field (a rational form with an adelic point,
  classes as double cosets, mass as a class sum): `New.Space`, `New.mass` in
  `grh/src/Lib/Adelic/Unitary/Defs.lean` of the Lean 4 formalization of GRH for Dirichlet
  L-functions, https://github.com/lsernau/grh-lean (Apache 2.0).
* The finite adeles are Mathlib's `IsDedekindDomain.FiniteAdeleRing ℤ ℚ`.
-/

@[expose] public noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TensorProduct Module

namespace AdelicGenus

/-- The finite adeles of `ℚ`. -/
abbrev Af : Type := FiniteAdeleRing ℤ ℚ

/-- The rationals integral at every prime other than `2`, i.e. `Z[1/2]`. -/
def dyadic : Subring ℚ where
  carrier := {q | ∀ v : HeightOneSpectrum ℤ, (2 : ℤ) ∉ v.asIdeal → v.valuation ℚ q ≤ 1}
  mul_mem' {a b} ha hb v hv := by
    rw [map_mul]
    exact mul_le_one' (ha v hv) (hb v hv)
  one_mem' v _ := by rw [map_one]
  add_mem' {a b} ha hb v hv := (Valuation.map_add _ _ _).trans (max_le (ha v hv) (hb v hv))
  zero_mem' v _ := by
    rw [map_zero]
    exact zero_le
  neg_mem' {a} ha v hv := by
    rw [Valuation.map_neg]
    exact ha v hv

/-- The finite adeles integral at every prime other than `2`. -/
def dyadicAdeles : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum ℤ, (2 : ℤ) ∉ v.asIdeal →
    a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' {a b} ha hb v hv := by
    change a v * b v ∈ _
    exact mul_mem (ha v hv) (hb v hv)
  one_mem' v _ := by
    change (1 : v.adicCompletion ℚ) ∈ _
    exact one_mem _
  add_mem' {a b} ha hb v hv := by
    change a v + b v ∈ _
    exact add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := by
    change (0 : v.adicCompletion ℚ) ∈ _
    exact zero_mem _
  neg_mem' {a} ha v hv := by
    change -a v ∈ _
    exact neg_mem (ha v hv)

/-- A rational number is integral at every odd prime of the adeles exactly when it is in
`Z[1/2]`. -/
theorem algebraMap_mem_dyadicAdeles {q : ℚ} :
    algebraMap ℚ Af q ∈ dyadicAdeles ↔ q ∈ dyadic := by
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  change Valued.v (algebraMap ℚ Af q v) ≤ 1 ↔ _
  rw [FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation']

/-- The point of `Spec ℤ` of a prime number. -/
def primeSpectrum (p : ℕ) (hp : p.Prime) : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)}, (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
    (Nat.prime_iff_prime_int.1 hp), by simpa using hp.ne_zero⟩

theorem valuation_intCast (v : HeightOneSpectrum ℤ) (r : ℤ) :
    v.valuation ℚ (r : ℚ) = v.intValuation r := by
  rw [← eq_intCast (algebraMap ℤ ℚ) r]
  exact valuation_of_algebraMap v r

/-- The valuation of `2` is `1` at every prime not containing `2`. -/
theorem valuation_two {v : HeightOneSpectrum ℤ} (hv : (2 : ℤ) ∉ v.asIdeal) :
    v.valuation ℚ 2 = 1 := by
  have h := valuation_intCast v 2
  push_cast at h
  rw [h, intValuation_eq_one_iff]
  exact hv

/-- **`dyadic` is `Z[1/2]`**: a rational number is integral at every prime other than `2` exactly
when it is the image of an element of `ZHalf`. -/
theorem mem_dyadic_iff {q : ℚ} : q ∈ dyadic ↔ ∃ z : ZHalf, ZHalf.toRat z = q := by
  constructor
  · intro hq
    have hden : ∀ {p : ℕ}, p.Prime → p ∣ q.den → p = 2 := by
      intro p hp hpd
      by_contra hp2
      set v := primeSpectrum p hp
      have hv2 : (2 : ℤ) ∉ v.asIdeal := by
        intro h
        have h' : (p : ℤ) ∣ 2 := Ideal.mem_span_singleton.1 h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (by exact_mod_cast h'))
      have hd : v.valuation ℚ (q.den : ℤ) < 1 := by
        rw [valuation_intCast, intValuation_lt_one_iff_mem]
        exact Ideal.mem_span_singleton.2 (by exact_mod_cast hpd)
      have hn : v.valuation ℚ q.num = 1 := by
        rw [valuation_intCast, intValuation_eq_one_iff]
        intro h
        have hpn : (p : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 h
        have hpn' : p ∣ q.num.natAbs := Int.natCast_dvd.1 hpn
        exact hp.not_dvd_one (by
          rw [← Nat.Coprime.gcd_eq_one q.reduced]
          exact Nat.dvd_gcd hpn' hpd)
      have hmul : v.valuation ℚ q * v.valuation ℚ (q.den : ℤ) = v.valuation ℚ q.num := by
        rw [← map_mul]
        congr 1
        push_cast
        exact Rat.mul_den_eq_num q
      have := (mul_le_of_le_one_left' (hq v hv2)).trans_lt hd
      rw [hmul, hn] at this
      exact lt_irrefl _ this
    obtain hk := Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz hden
    set k := q.den.primeFactorsList.length
    let t : ZHalf := IsLocalization.Away.invSelf (2 : ℤ)
    have ht : ZHalf.toRat t * 2 = 1 := by
      have := congrArg ZHalf.toRat (IsLocalization.Away.mul_invSelf (S := ZHalf) (2 : ℤ))
      rw [map_mul, map_one, eq_intCast (algebraMap ℤ ZHalf), ZHalf.toRat_intCast] at this
      rw [mul_comm]
      exact_mod_cast this
    have h2 : ZHalf.toRat t = 1 / 2 := by
      rw [eq_div_iff (two_ne_zero)]
      exact ht
    refine ⟨(q.num : ZHalf) * t ^ k, ?_⟩
    rw [map_mul, map_pow, ZHalf.toRat_intCast, h2, one_div, inv_pow, ← div_eq_mul_inv,
      show (2 : ℚ) ^ k = q.den by exact_mod_cast hk.symm]
    exact Rat.num_div_den q
  · rintro ⟨z, rfl⟩ v hv
    obtain ⟨m, w, hw⟩ := ZHalf.exists_pow_mul_toRat z
    have hw' : v.valuation ℚ ((2 : ℚ) ^ m * ZHalf.toRat z) ≤ 1 := by
      rw [hw, valuation_intCast]
      exact intValuation_le_one v w
    rwa [map_mul, map_pow, valuation_two hv, one_pow, one_mul] at hw'

/-- The prime `3`, a point of `Spec ℤ`. -/
def three : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {3}, (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_three, by simp⟩

instance : Nontrivial Af :=
  ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun a : Af => a three) h)⟩⟩

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The base change `E → 𝔸_f ⊗ E`, `x ↦ 1 ⊗ x`. -/
noncomputable def toAf : E →ₗ[ℚ] Af ⊗[ℚ] E := TensorProduct.mk ℚ Af E 1

theorem toAf_apply (x : E) : toAf x = (1 : Af) ⊗ₜ[ℚ] x := rfl

theorem toAf_injective : Function.Injective (toAf (E := E)) := by
  have hinj : Function.Injective (LinearMap.rTensor E (Algebra.linearMap ℚ Af)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap ℚ Af).injective
  intro x y hxy
  apply (TensorProduct.lid ℚ E).symm.injective
  apply hinj
  simpa [toAf_apply] using hxy

theorem toAf_smul (q : ℚ) (x : E) : toAf (q • x) = algebraMap ℚ Af q • toAf x := by
  rw [map_smul, algebraMap_smul]

section Stab

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The isometries of `β` preserving every set `S i`. -/
def stabSub (β : LinearMap.BilinForm R M) {ι : Type*} (S : ι → Set M) :
    Subgroup (M ≃ₗ[R] M) where
  carrier := {g | (∀ x y, β (g x) (g y) = β x y) ∧ ∀ i x, g x ∈ S i ↔ x ∈ S i}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩
  mul_mem' {g h} hg hh := ⟨fun x y => (hg.1 (h x) (h y)).trans (hh.1 x y),
    fun i x => (hg.2 i (h x)).trans (hh.2 i x)⟩
  inv_mem' {g} hg := ⟨fun x y => by
      change β (g.symm x) (g.symm y) = β x y
      rw [← hg.1, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply],
    fun i x => by
      change g.symm x ∈ S i ↔ x ∈ S i
      rw [← hg.2 i, LinearEquiv.apply_symm_apply]⟩

theorem mem_stabSub {β : LinearMap.BilinForm R M} {ι : Type*} {S : ι → Set M}
    {g : M ≃ₗ[R] M} :
    g ∈ stabSub β S ↔ (∀ x y, β (g x) (g y) = β x y) ∧ ∀ i x, g x ∈ S i ↔ x ∈ S i := Iff.rfl

end Stab

/-- Base change of automorphisms, `γ ↦ 1 ⊗ γ`. -/
noncomputable def baseChangeHom : (E ≃ₗ[ℚ] E) →* (Af ⊗[ℚ] E ≃ₗ[Af] Af ⊗[ℚ] E) where
  toFun := LinearEquiv.baseChange ℚ Af E E
  map_one' := LinearEquiv.baseChange_one ℚ Af E
  map_mul' g h := LinearEquiv.baseChange_trans ℚ Af E E h g

theorem baseChangeHom_toAf (γ : E ≃ₗ[ℚ] E) (x : E) :
    baseChangeHom γ (toAf x) = toAf (γ x) := by
  simp [baseChangeHom, toAf_apply]

theorem baseChangeHom_injective : Function.Injective (baseChangeHom (E := E)) := by
  intro γ γ' h
  ext x
  apply toAf_injective
  rw [← baseChangeHom_toAf, ← baseChangeHom_toAf, h]

theorem baseChangeHom_isometry (B : LinearMap.BilinForm ℚ E) {γ : E ≃ₗ[ℚ] E}
    (hγ : ∀ x y, B (γ x) (γ y) = B x y) (x y : Af ⊗[ℚ] E) :
    B.baseChange Af (baseChangeHom γ x) (baseChangeHom γ y) = B.baseChange Af x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul a' m' =>
      simp [baseChangeHom, LinearMap.BilinForm.baseChange_tmul, hγ]

variable (B : LinearMap.BilinForm ℚ E) {ι : Type*} {κ : ι → Type*} (b : ∀ i, κ i → E)

/-- The member `Lᵢ`: the `Z[1/2]`-span of `bᵢ`. -/
def member (i : ι) : Submodule dyadic E := Submodule.span dyadic (Set.range (b i))

/-- The `ℚ`-span `Wᵢ` of `bᵢ`. -/
def memberSpan (i : ι) : Submodule ℚ E := Submodule.span ℚ (Set.range (b i))

/-- The `𝔸_f`-span `𝔸_f Wᵢ` of `bᵢ`. -/
def adelicSpan (i : ι) : Submodule Af (Af ⊗[ℚ] E) :=
  Submodule.span Af (Set.range fun k => toAf (b i k))

/-- The span `Ô' Lᵢ` of `bᵢ` over the adeles integral at every odd prime. -/
def adelicMember (i : ι) : Submodule dyadicAdeles (Af ⊗[ℚ] E) :=
  Submodule.span dyadicAdeles (Set.range fun k => toAf (b i k))

/-- The rational group `G(ℚ)`: isometries of `E` preserving every `Wᵢ`. -/
def ratGroup : Subgroup (E ≃ₗ[ℚ] E) := stabSub B fun i => (memberSpan b i : Set E)

/-- The automorphisms of the chain: isometries of `E` preserving every member `Lᵢ`. -/
def chainAut : Subgroup (E ≃ₗ[ℚ] E) := stabSub B fun i => (member b i : Set E)

/-- The adelic group `G(𝔸_f)`: isometries of `𝔸_f ⊗ E` preserving every `𝔸_f Wᵢ`. -/
def adelicGroup : Subgroup (Af ⊗[ℚ] E ≃ₗ[Af] Af ⊗[ℚ] E) :=
  stabSub (B.baseChange Af) fun i => (adelicSpan b i : Set (Af ⊗[ℚ] E))

/-- The isometries of `𝔸_f ⊗ E` preserving every `Ô' Lᵢ`. -/
def adelicStab : Subgroup (Af ⊗[ℚ] E ≃ₗ[Af] Af ⊗[ℚ] E) :=
  stabSub (B.baseChange Af) fun i => (adelicMember b i : Set (Af ⊗[ℚ] E))

/-- The rational points `Γ` inside `G(𝔸_f)`. -/
noncomputable def ratImage : Subgroup (adelicGroup B b) :=
  ((ratGroup B b).map baseChangeHom).subgroupOf (adelicGroup B b)

/-- The level `K` inside `G(𝔸_f)`: the stabilizer of every `Ô' Lᵢ`. -/
def adelicLevel : Subgroup (adelicGroup B b) := (adelicStab B b).subgroupOf (adelicGroup B b)

/-- **The genus** of the chain: the double coset space `Γ \ G(𝔸_f) / K`. -/
def genus : Type _ := DoubleCoset.Quotient (ratImage B b : Set (adelicGroup B b)) (adelicLevel B b)

/-- **The mass** of the genus: `∑ 1 / #(Γ ∩ g K g⁻¹)` over the classes. -/
noncomputable def genusMass : ℚ := DoubleCoset.mass (ratImage B b) (adelicLevel B b)

variable {B b}

theorem toAf_mem_adelicSpan {i : ι} {x : E} (hx : x ∈ memberSpan b i) :
    toAf x ∈ adelicSpan b i := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Submodule.subset_span ⟨k, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul q y _ hy => rw [toAf_smul]; exact Submodule.smul_mem _ _ hy

theorem toAf_mem_adelicMember {i : ι} {x : E} (hx : x ∈ member b i) :
    toAf x ∈ adelicMember b i := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact Submodule.subset_span ⟨k, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul q y _ hy =>
    have : toAf (q • y) =
        (⟨algebraMap ℚ Af q, algebraMap_mem_dyadicAdeles.2 q.2⟩ : dyadicAdeles) • toAf y :=
      toAf_smul (q : ℚ) y
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem member_le_memberSpan {i : ι} {x : E} (hx : x ∈ member b i) : x ∈ memberSpan b i := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul q y _ hy => exact Submodule.smul_mem _ (q : ℚ) hy

/-- **Recovering a member from its adelic span**: for `bᵢ` linearly independent over `ℚ`, a vector
of `Wᵢ` whose image lies in `Ô' Lᵢ` lies in `Lᵢ`. -/
theorem mem_member_of_toAf_mem {i : ι} [Fintype (κ i)] (hb : LinearIndependent ℚ (b i)) {x : E}
    (hx : x ∈ memberSpan b i) (hA : toAf x ∈ adelicMember b i) : x ∈ member b i := by
  let W := Submodule.span ℚ (Set.range (b i))
  have hx' : x ∈ W := hx
  let bW : Basis (κ i) ℚ W := Basis.span hb
  have hbW : ∀ k, ((bW k : W) : E) = b i k := fun k =>
    congrArg Subtype.val (Basis.span_apply hb k)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun dyadicAdeles).1 hA
  -- compare coordinates in `𝔸_f ⊗ Wᵢ`, which embeds in `𝔸_f ⊗ E`
  have hinj : Function.Injective (W.subtype.baseChange Af) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ W.injective_subtype
  have heq : (∑ k, (a k : Af) • Algebra.TensorProduct.basis Af bW k) =
      (1 : Af) ⊗ₜ[ℚ] (⟨x, hx'⟩ : W) := by
    apply hinj
    rw [map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, ← toAf_apply, ← ha]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
      Submodule.subtype_apply, hbW]
    rfl
  have hcoord : ∀ k, algebraMap ℚ Af (bW.repr ⟨x, hx'⟩ k) = a k := by
    intro k
    have := congrArg (fun z => (Algebra.TensorProduct.basis Af bW).repr z k) heq
    simp only [map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_repr_tmul,
      one_smul, Finsupp.mapRange_apply] at this
    rw [← this, Finset.sum_eq_single k (fun c _ hc => by rw [Finsupp.single_eq_of_ne' hc,
      mul_zero]) (by simp), Finsupp.single_eq_same, mul_one]
  have hdy : ∀ k, bW.repr ⟨x, hx'⟩ k ∈ dyadic := fun k =>
    algebraMap_mem_dyadicAdeles.1 (by rw [hcoord k]; exact (a k).2)
  have hsum : x = ∑ k, bW.repr ⟨x, hx'⟩ k • b i k := by
    have := congrArg Subtype.val (bW.sum_repr ⟨x, hx'⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hbW] at this
    exact this.symm
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have : bW.repr ⟨x, hx'⟩ k • b i k = (⟨_, hdy k⟩ : dyadic) • b i k := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The image of a rational isometry preserving every `Wᵢ` is in `G(𝔸_f)`. -/
theorem baseChangeHom_mem_adelicGroup {γ : E ≃ₗ[ℚ] E} (hγ : γ ∈ ratGroup B b) :
    baseChangeHom γ ∈ adelicGroup B b := by
  have hγ' : γ⁻¹ ∈ ratGroup B b := inv_mem hγ
  have key : ∀ g : E ≃ₗ[ℚ] E, g ∈ ratGroup B b → ∀ i y, y ∈ adelicSpan b i →
      baseChangeHom g y ∈ adelicSpan b i := by
    intro g hg i y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      rw [baseChangeHom_toAf]
      exact toAf_mem_adelicSpan ((hg.2 i _).2 (Submodule.subset_span ⟨k, rfl⟩))
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
  refine ⟨baseChangeHom_isometry B hγ.1, fun i y => ⟨fun h => ?_, key γ hγ i y⟩⟩
  have := key γ⁻¹ hγ' i _ h
  have e : baseChangeHom γ⁻¹ (baseChangeHom γ y) = y := by
    rw [map_inv]
    exact (baseChangeHom γ).symm_apply_apply y
  rwa [e] at this

/-- An automorphism of the chain preserves every `Wᵢ`. -/
theorem chainAut_le_ratGroup : chainAut B b ≤ ratGroup B b := by
  have key : ∀ g : E ≃ₗ[ℚ] E, g ∈ chainAut B b → ∀ i y, y ∈ memberSpan b i →
      g y ∈ memberSpan b i := by
    intro g hg i y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact member_le_memberSpan ((hg.2 i _).2 (Submodule.subset_span ⟨k, rfl⟩))
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
  intro γ hγ
  refine ⟨hγ.1, fun i y => ⟨fun h => ?_, key γ hγ i y⟩⟩
  have := key γ⁻¹ (inv_mem hγ) i _ h
  rwa [show γ⁻¹ (γ y) = y from γ.symm_apply_apply y] at this

/-- An automorphism of the chain extends to an element of the level. -/
theorem baseChangeHom_mem_adelicStab {γ : E ≃ₗ[ℚ] E} (hγ : γ ∈ chainAut B b) :
    baseChangeHom γ ∈ adelicStab B b := by
  have key : ∀ g : E ≃ₗ[ℚ] E, g ∈ chainAut B b → ∀ i y, y ∈ adelicMember b i →
      baseChangeHom g y ∈ adelicMember b i := by
    intro g hg i y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      rw [baseChangeHom_toAf]
      exact toAf_mem_adelicMember ((hg.2 i _).2 (Submodule.subset_span ⟨k, rfl⟩))
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : baseChangeHom g (c • y) = c • baseChangeHom g y :=
        (baseChangeHom g).map_smul (c : Af) y
      rw [this]
      exact Submodule.smul_mem _ _ hy
  refine ⟨baseChangeHom_isometry B hγ.1, fun i y => ⟨fun h => ?_, key γ hγ i y⟩⟩
  have := key γ⁻¹ (inv_mem hγ) i _ h
  have e : baseChangeHom γ⁻¹ (baseChangeHom γ y) = y := by
    rw [map_inv]
    exact (baseChangeHom γ).symm_apply_apply y
  rwa [e] at this

/-- A rational isometry preserving every `Wᵢ` whose base change is in the level maps every member
into itself. -/
theorem mem_member_of_mem_adelicStab (hb : ∀ i, LinearIndependent ℚ (b i))
    [∀ i, Fintype (κ i)] {γ : E ≃ₗ[ℚ] E} (hγ : γ ∈ ratGroup B b)
    (hK : baseChangeHom γ ∈ adelicStab B b) {i : ι} {y : E} (hy : y ∈ member b i) :
    γ y ∈ member b i := by
  refine mem_member_of_toAf_mem (hb i) ((hγ.2 i y).2 (member_le_memberSpan hy)) ?_
  rw [← baseChangeHom_toAf]
  exact (hK.2 i _).2 (toAf_mem_adelicMember hy)

/-- **The class of `1` in the genus**: the stabilizer `Γ ∩ K` is the automorphism group of the
chain, the isometries of `E` preserving every member `Lᵢ`. -/
theorem card_classAut_one (hb : ∀ i, LinearIndependent ℚ (b i)) [∀ i, Fintype (κ i)] :
    Nat.card (DoubleCoset.classAut (ratImage B b) (adelicLevel B b) 1) = Nat.card (chainAut B b) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨⟨baseChangeHom γ.1,
    baseChangeHom_mem_adelicGroup (chainAut_le_ratGroup γ.2)⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [DoubleCoset.mem_classAut, inv_one, one_mul, mul_one]
    exact ⟨Subgroup.mem_subgroupOf.2 ⟨γ.1, chainAut_le_ratGroup γ.2, rfl⟩,
      Subgroup.mem_subgroupOf.2 (baseChangeHom_mem_adelicStab γ.2)⟩
  · intro γ γ' h
    exact Subtype.ext (baseChangeHom_injective
      (congrArg (fun δ : DoubleCoset.classAut (ratImage B b) (adelicLevel B b) 1 =>
        ((δ : adelicGroup B b) : Af ⊗[ℚ] E ≃ₗ[Af] Af ⊗[ℚ] E)) h))
  · rintro ⟨δ, hδ⟩
    rw [DoubleCoset.mem_classAut, inv_one, one_mul, mul_one] at hδ
    obtain ⟨hΓ, hK⟩ := hδ
    obtain ⟨γ, hγ, hγδ⟩ := Subgroup.mem_subgroupOf.1 hΓ
    have hK' : baseChangeHom γ ∈ adelicStab B b := by
      rw [hγδ]
      exact Subgroup.mem_subgroupOf.1 hK
    have hγinv : γ⁻¹ ∈ ratGroup B b := inv_mem hγ
    have hKinv : baseChangeHom γ⁻¹ ∈ adelicStab B b := by
      rw [map_inv]
      exact inv_mem hK'
    have hchain : γ ∈ chainAut B b := ⟨hγ.1, fun i y => ⟨fun h => by
      have := mem_member_of_mem_adelicStab hb hγinv hKinv h
      rwa [show γ⁻¹ (γ y) = y from γ.symm_apply_apply y] at this,
      mem_member_of_mem_adelicStab hb hγ hK'⟩⟩
    exact ⟨⟨γ, hchain⟩, Subtype.ext (Subtype.ext hγδ)⟩

end AdelicGenus
