module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Int

/-!
# Minkowski's lemma: congruence kernels of `GL_N(ℤ)` are torsion-free

For every level `m ≥ 3`, the kernel of reduction `GL_N(ℤ) → GL_N(ℤ/m)` is torsion-free
(`Matrix.eq_one_of_pow_eq_one_of_modEq`), so every finite subgroup of `GL_N(ℤ)` embeds in
`GL_N(ℤ/m)` (`Matrix.injOn_reduce`). Level `3` is the case used for bounding finite subgroups;
level `2` fails (`-1` lies in the kernel).

The core is the prime-power case `Matrix.eq_one_of_pow_eq_one_of_modEq_prime_pow`: for a prime
`ℓ` and `g ≡ 1 (mod ℓᵏ)` with `k ≥ 1` (`k ≥ 2` if `ℓ = 2`), finite order forces `g = 1`. Reduce
to `g` of prime order `p` and write `g = 1 + ℓʲA` (`j ≥ k`).
* If `p ≠ ℓ`: `0 = gᵖ - 1 = (∑_{i<p} gⁱ) ℓʲA` and `∑_{i<p} gⁱ ≡ p (mod ℓ)`, so `ℓ ∣ A`.
* If `p = ℓ`: `0 = gˡ - 1 = ℓʲ⁺¹A + (terms divisible by ℓʲ⁺²)`, by the binomial theorem, since
  `ℓ` divides the middle binomial coefficients and `ℓj ≥ j + 2`. So `ℓ ∣ A`.
Hence `g - 1` is divisible by every power of `ℓ`, so it is zero.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every entry of `X` is divisible by `c`. -/
def EntriesDvd (c : ℤ) (X : Matrix n n ℤ) : Prop := ∀ a b, c ∣ X a b

namespace EntriesDvd

variable {c d : ℤ} {X Y : Matrix n n ℤ}

omit [Fintype n] [DecidableEq n] in
theorem zero : EntriesDvd c (0 : Matrix n n ℤ) := fun _ _ => dvd_zero c

omit [Fintype n] [DecidableEq n] in
theorem add (hX : EntriesDvd c X) (hY : EntriesDvd c Y) : EntriesDvd c (X + Y) :=
  fun a b => dvd_add (hX a b) (hY a b)

omit [Fintype n] [DecidableEq n] in
theorem neg (hX : EntriesDvd c X) : EntriesDvd c (-X) := fun a b => (hX a b).neg_right

omit [Fintype n] [DecidableEq n] in
theorem smul (r : ℤ) (hX : EntriesDvd c X) : EntriesDvd c (r • X) :=
  fun a b => dvd_mul_of_dvd_right (hX a b) r

omit [Fintype n] [DecidableEq n] in
theorem smul_self (c : ℤ) (X : Matrix n n ℤ) : EntriesDvd c (c • X) :=
  fun a b => dvd_mul_right c (X a b)

omit [Fintype n] [DecidableEq n] in
theorem of_dvd (h : c ∣ d) (hX : EntriesDvd d X) : EntriesDvd c X := fun a b => h.trans (hX a b)

omit [DecidableEq n] in
theorem mul_right (hX : EntriesDvd c X) (Y : Matrix n n ℤ) : EntriesDvd c (X * Y) :=
  fun a b => Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (hX a l) (Y l b)

omit [Fintype n] [DecidableEq n] in
theorem sum {ι : Type*} {s : Finset ι} {f : ι → Matrix n n ℤ} (h : ∀ i ∈ s, EntriesDvd c (f i)) :
    EntriesDvd c (∑ i ∈ s, f i) := fun a b => by
  rw [Matrix.sum_apply]
  exact Finset.dvd_sum fun i hi => h i hi a b

omit [Fintype n] [DecidableEq n] in
/-- Cancelling a common nonzero factor. -/
theorem cancel (hc : c ≠ 0) (h : EntriesDvd (c * d) (c • X)) : EntriesDvd d X :=
  fun a b => Int.dvd_of_mul_dvd_mul_left hc (h a b)

omit [Fintype n] [DecidableEq n] in
theorem exists_eq_smul (h : EntriesDvd c X) : ∃ Y : Matrix n n ℤ, X = c • Y :=
  ⟨Matrix.of fun a b => (h a b).choose, by ext a b; exact (h a b).choose_spec⟩

omit [Fintype n] [DecidableEq n] in
/-- A matrix whose entries are divisible by every power of a prime is zero. -/
theorem eq_zero_of_forall_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ∀ k, EntriesDvd ((ℓ : ℤ) ^ k) X) :
    X = 0 := by
  ext a b
  by_contra hx
  have := Int.natAbs_le_of_dvd_ne_zero (h (X a b).natAbs a b) hx
  rw [Int.natAbs_pow, Int.natAbs_natCast] at this
  have h2 : (X a b).natAbs < ℓ ^ (X a b).natAbs := Nat.lt_pow_self hℓ.one_lt
  exact absurd this (not_le.2 h2)

end EntriesDvd

/-- Congruence to `1` is preserved by powers. -/
theorem entriesDvd_pow_sub_one {c : ℤ} {g : Matrix n n ℤ} (hg : EntriesDvd c (g - 1)) (i : ℕ) :
    EntriesDvd c (g ^ i - 1) := by
  induction i with
  | zero => simpa using EntriesDvd.zero
  | succ i ih =>
    have : g ^ (i + 1) - 1 = (g ^ i - 1) * g + (g - 1) := by
      rw [pow_succ, sub_mul, one_mul]
      abel
    rw [this]
    exact (ih.mul_right g).add hg

theorem mul_natCast_eq_smul (X : Matrix n n ℤ) (k : ℕ) : X * (k : Matrix n n ℤ) = (k : ℤ) • X := by
  rw [← Nat.cast_comm, ← nsmul_eq_mul, natCast_zsmul]

theorem smul_pow' (c : ℤ) (A : Matrix n n ℤ) (m : ℕ) : (c • A) ^ m = c ^ m • A ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, pow_succ, pow_succ, smul_mul_smul_comm]

/-- The descent step: if `g = 1 + ℓʲA` (`j ≥ 1`, and `j ≥ 2` when `ℓ = 2`) has prime order `p`,
then `ℓ ∣ A`. -/
theorem entriesDvd_of_pow_prime {ℓ p j : ℕ} (hℓ : ℓ.Prime) (hj : 1 ≤ j) (hj2 : ℓ = 2 → 2 ≤ j)
    (hp : p.Prime) {g A : Matrix n n ℤ} (hgA : g - 1 = ((ℓ : ℤ) ^ j) • A) (hgp : g ^ p = 1) :
    EntriesDvd (ℓ : ℤ) A := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hg : g = ((ℓ : ℤ) ^ j) • A + 1 := by rw [← hgA]; abel
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
    set D := ((p : ℤ) ^ j) • A with hD
    -- binomial expansion of `(D + 1)ᵖ`
    have hbin := (Commute.one_right D).add_pow p
    rw [← hg, hgp] at hbin
    conv_rhs at hbin => rw [hq, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, zero_add] at hbin
    have hsum := add_eq_right.1 hbin.symm
    -- the terms of degree `≥ 2` are divisible by `p ^ (j + 2)`
    have hrest : EntriesDvd ((p : ℤ) ^ (j + 2))
        (∑ i ∈ Finset.range (q + 1), D ^ (i + 1 + 1) *
          (((q + 2).choose (i + 1 + 1) : ℕ) : Matrix n n ℤ)) := by
      refine EntriesDvd.sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [mul_natCast_eq_smul, hD, smul_pow', smul_smul]
      refine (EntriesDvd.smul_self _ _).of_dvd ?_
      rw [← pow_mul]
      by_cases hip : i + 1 + 1 < q + 2
      · have h1 : (p : ℤ) ∣ ((q + 2).choose (i + 1 + 1) : ℕ) := by
          rw [← hq]
          exact_mod_cast hp.dvd_choose_self (by omega) (by omega)
        have h2 : (p : ℤ) ^ (j + 1) ∣ (p : ℤ) ^ (j * (i + 1 + 1)) :=
          pow_dvd_pow _ (by nlinarith)
        rw [pow_succ']
        exact mul_dvd_mul h1 h2
      · have hi' : i + 1 + 1 = q + 2 := by omega
        rw [hi', Nat.choose_self, Nat.cast_one, one_mul]
        refine pow_dvd_pow _ ?_
        rcases Nat.lt_or_ge 2 p with h3 | h3
        · nlinarith
        · have hp2 : p = 2 := le_antisymm h3 hp.two_le
          have := hj2 hp2
          nlinarith
    -- so `p ^ (j + 1) • A = -(rest)` is divisible by `p ^ (j + 2)`
    have hlin : ((p : ℤ) ^ (j + 1)) • A = -(∑ i ∈ Finset.range (q + 1), D ^ (i + 1 + 1) *
        (((q + 2).choose (i + 1 + 1) : ℕ) : Matrix n n ℤ)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm, ← hsum, mul_natCast_eq_smul, hD, smul_smul, ← hq,
        pow_succ']
    have := hrest.neg
    rw [← hlin, pow_succ (p : ℤ) (j + 1)] at this
    exact this.cancel (pow_ne_zero _ hℓ0)
  · -- `∑_{i<p} gⁱ ≡ p (mod ℓ)`
    set Q := ∑ i ∈ Finset.range p, g ^ i
    have hQA : Q * A = 0 := by
      have h := geom_sum_mul g p
      rw [hgp, sub_self, hgA, Matrix.mul_smul] at h
      exact smul_right_injective _ (pow_ne_zero j hℓ0) (h.trans (smul_zero _).symm)
    have hR : EntriesDvd (ℓ : ℤ) (∑ i ∈ Finset.range p, (g ^ i - 1)) :=
      EntriesDvd.sum fun i _ => entriesDvd_pow_sub_one
        ((EntriesDvd.smul_self _ A).of_dvd (dvd_pow_self _ (by omega)) |> fun h => hgA ▸ h) i
    have hQ : Q = p • (1 : Matrix n n ℤ) + ∑ i ∈ Finset.range p, (g ^ i - 1) := by
      simp only [Q, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      abel
    rw [hQ, add_mul, smul_mul_assoc, one_mul] at hQA
    intro a b
    have hab := congrFun (congrFun hQA a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply] at hab
    rw [nsmul_eq_mul] at hab
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) * A a b := by
      have := (hR.mul_right A) a b
      rw [eq_neg_of_add_eq_zero_left hab]
      exact this.neg_right
    have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
    rcases hprime.dvd_or_dvd h3 with h | h
    · exfalso
      have : ℓ ∣ p := by exact_mod_cast h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 this).symm
    · exact h

/-- Prime order at a prime-power level: `g ≡ 1 (mod ℓᵏ)` of prime order is `1`. -/
theorem eq_one_of_pow_prime_of_modEq_prime_pow {ℓ k p : ℕ} (hℓ : ℓ.Prime) (hk : 1 ≤ k)
    (hk2 : ℓ = 2 → 2 ≤ k) (hp : p.Prime) {g : Matrix n n ℤ}
    (hg : EntriesDvd ((ℓ : ℤ) ^ k) (g - 1)) (hgp : g ^ p = 1) : g = 1 := by
  have hall : ∀ j, k ≤ j → EntriesDvd ((ℓ : ℤ) ^ j) (g - 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hg
    | succ j hkj ih =>
      obtain ⟨A, hA⟩ := ih.exists_eq_smul
      obtain ⟨A', rfl⟩ := (entriesDvd_of_pow_prime hℓ (by omega) (fun h => by have := hk2 h; omega)
        hp hA hgp).exists_eq_smul
      rw [hA, smul_smul, ← pow_succ]
      exact EntriesDvd.smul_self _ _
  rw [← sub_eq_zero]
  exact EntriesDvd.eq_zero_of_forall_pow hℓ fun j =>
    (hall (max j k) (le_max_right _ _)).of_dvd (pow_dvd_pow _ (le_max_left _ _))

/-- **Minkowski's lemma at a prime-power level**: for a prime `ℓ` and `k ≥ 1` (`k ≥ 2` when
`ℓ = 2`), an integer matrix `g ≡ 1 (mod ℓᵏ)` of finite order is `1`. -/
theorem eq_one_of_pow_eq_one_of_modEq_prime_pow {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : 1 ≤ k)
    (hk2 : ℓ = 2 → 2 ≤ k) {g : Matrix n n ℤ} (hg : EntriesDvd ((ℓ : ℤ) ^ k) (g - 1)) {r : ℕ}
    (hr : r ≠ 0) (hgr : g ^ r = 1) : g = 1 := by
  by_contra hg1
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.2 ⟨r, Nat.pos_of_ne_zero hr, hgr⟩
  have hd1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  set h := g ^ (orderOf g / p)
  have hord : orderOf h = p := orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hpd
  have hhp : h ^ p = 1 := by
    have := pow_orderOf_eq_one h
    rwa [hord] at this
  have := eq_one_of_pow_prime_of_modEq_prime_pow hℓ hk hk2 hp
    (entriesDvd_pow_sub_one hg (orderOf g / p)) hhp
  rw [← orderOf_eq_one_iff, hord] at this
  exact hp.one_lt.ne' this

/-- **Minkowski's lemma**: for every level `m ≥ 3`, an integer matrix `g ≡ 1 (mod m)` of finite
order is `1`. -/
theorem eq_one_of_pow_eq_one_of_modEq {m : ℕ} (hm : 3 ≤ m) {g : Matrix n n ℤ}
    (hg : EntriesDvd (m : ℤ) (g - 1)) {r : ℕ} (hr : r ≠ 0) (hgr : g ^ r = 1) : g = 1 := by
  by_cases h4 : 4 ∣ m
  · exact eq_one_of_pow_eq_one_of_modEq_prime_pow Nat.prime_two (k := 2) (by norm_num)
      (fun _ => le_rfl) (hg.of_dvd (by exact_mod_cast h4)) hr hgr
  · obtain ⟨q, hq, hqm, hq2⟩ : ∃ q, q.Prime ∧ q ∣ m ∧ q ≠ 2 := by
      by_contra hno
      push Not at hno
      have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : m ≠ 0)
        (fun {d} hd hdm => hno d hd hdm)
      set e := m.primeFactorsList.length
      have he : 2 ≤ e := by
        by_contra he
        interval_cases e <;> omega
      exact h4 (hpow ▸ (pow_dvd_pow 2 he : 2 ^ 2 ∣ 2 ^ e))
    exact eq_one_of_pow_eq_one_of_modEq_prime_pow hq (k := 1) le_rfl (fun h => absurd h hq2)
      (hg.of_dvd (by rw [pow_one]; exact_mod_cast hqm)) hr hgr

/-- Reduction modulo `m` of invertible integer matrices. -/
def reduce (m : ℕ) : GL n ℤ →* GL n (ZMod m) :=
  Units.map (Int.castRingHom (ZMod m)).mapMatrix.toMonoidHom

/-- **Minkowski's lemma, finite subgroups**: for `m ≥ 3`, every finite subgroup of `GL_N(ℤ)` embeds
in `GL_N(ℤ/m)` under reduction. -/
theorem injOn_reduce {m : ℕ} (hm : 3 ≤ m) (H : Subgroup (GL n ℤ)) [Finite H] :
    Set.InjOn (reduce (n := n) m) H := by
  have _ : NeZero m := ⟨by omega⟩
  intro x hx y hy hxy
  set z : H := ⟨x⁻¹ * y, H.mul_mem (H.inv_mem hx) hy⟩
  have hz1 : reduce m (z : GL n ℤ) = 1 := by
    change reduce m (x⁻¹ * y) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hz : ∀ a b, ((((z : GL n ℤ) : Matrix n n ℤ) a b : ℤ) : ZMod m) =
      (1 : Matrix n n (ZMod m)) a b := fun a b =>
    congrArg (fun u : GL n (ZMod m) => (u : Matrix n n (ZMod m)) a b) hz1
  have hdvd : EntriesDvd (m : ℤ) (((z : GL n ℤ) : Matrix n n ℤ) - 1) := by
    intro a b
    have key : ((((z : GL n ℤ) : Matrix n n ℤ) a b - (1 : Matrix n n ℤ) a b : ℤ) : ZMod m) = 0 := by
      push_cast
      rw [hz a b]
      by_cases hab : a = b
      · subst hab
        simp
      · simp [Matrix.one_apply_ne hab]
    rw [Matrix.sub_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 key
  have hfin := isOfFinOrder_of_finite z
  have hmat : ((z : GL n ℤ) : Matrix n n ℤ) ^ orderOf z = 1 := by
    have := congrArg (fun u : H => (((u : GL n ℤ)) : Matrix n n ℤ)) (pow_orderOf_eq_one z)
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at this
    exact this
  have hz' : (z : GL n ℤ) = 1 :=
    Units.ext (eq_one_of_pow_eq_one_of_modEq hm hdvd hfin.orderOf_pos.ne' hmat)
  change x⁻¹ * y = 1 at hz'
  exact inv_mul_eq_one.1 hz'

end Matrix
