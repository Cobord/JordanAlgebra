module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# The lowest-coefficient order on power series

For a totally ordered commutative ring `A`, order `A⟦X⟧` by declaring a nonzero series positive
when its lowest nonzero coefficient is positive. In this order `0 < X < a` for every `a > 0` in
`A`: the variable is a positive infinitesimal.

* `PowerSeries.lowestCoeff f`: the coefficient of `f` at its order (`0` for `f = 0`), with
  `lowestCoeff_mul` over a domain.
* `PowerSeriesLC A`: a type synonym for `A⟦X⟧` carrying this order, as a `LinearOrder` and an
  `IsStrictOrderedRing`, from the cone of series with nonnegative lowest coefficient.
  `PowerSeriesLC.le_iff`: `f ≤ g ↔ 0 ≤ lowestCoeff (g - f)`.
-/

@[expose] public section

noncomputable section

open PowerSeries

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-- The lowest coefficient of a power series: its coefficient at the order (`0` for `0`). -/
def lowestCoeff (f : A⟦X⟧) : A := coeff f.order.toNat f

@[simp]
theorem lowestCoeff_zero : lowestCoeff (0 : A⟦X⟧) = 0 := by simp [lowestCoeff]

theorem lowestCoeff_eq_zero_iff {f : A⟦X⟧} : lowestCoeff f = 0 ↔ f = 0 :=
  ⟨fun h => by_contra fun hf => coeff_order hf h, fun h => h ▸ lowestCoeff_zero⟩

/-- The lowest coefficient is the first nonzero one. -/
theorem lowestCoeff_eq {f : A⟦X⟧} {n : ℕ} (hn : coeff n f ≠ 0)
    (hlow : ∀ i < n, coeff i f = 0) : lowestCoeff f = coeff n f := by
  rw [lowestCoeff, order_eq_nat.2 ⟨hn, hlow⟩, ENat.toNat_natCast]

theorem lowestCoeff_neg (f : A⟦X⟧) : lowestCoeff (-f) = -lowestCoeff f := by
  rw [lowestCoeff, lowestCoeff, order_neg, map_neg]

theorem lowestCoeff_C {a : A} : lowestCoeff (C a) = a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, lowestCoeff_zero]
  · rw [lowestCoeff_eq (n := 0) (by rwa [coeff_zero_C]) (fun i hi => absurd hi (Nat.not_lt_zero i)),
      coeff_zero_C]

theorem lowestCoeff_one : lowestCoeff (1 : A⟦X⟧) = 1 := by
  rw [← map_one C, lowestCoeff_C]

theorem lowestCoeff_X_pow_mul {h : A⟦X⟧} (hc : constantCoeff h ≠ 0) (k : ℕ) :
    lowestCoeff (X ^ k * h) = constantCoeff h := by
  have hk : coeff k (X ^ k * h) = constantCoeff h := by
    simp [coeff_X_pow_mul', coeff_zero_eq_constantCoeff_apply]
  rw [lowestCoeff_eq (n := k) (by rwa [hk]), hk]
  intro i hi
  simp [coeff_X_pow_mul', not_le.2 hi]

/-- Over a domain the lowest coefficient is multiplicative. -/
theorem lowestCoeff_mul [NoZeroDivisors A] (f g : A⟦X⟧) :
    lowestCoeff (f * g) = lowestCoeff f * lowestCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  have hf' : constantCoeff (divXPowOrder f) = lowestCoeff f := constantCoeff_divXPowOrder
  have hg' : constantCoeff (divXPowOrder g) = lowestCoeff g := constantCoeff_divXPowOrder
  have hfg : f * g = X ^ (f.order.toNat + g.order.toNat) * (divXPowOrder f * divXPowOrder g) := by
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f), ← X_pow_order_mul_divXPowOrder (f := g)]
    ring
  have hc : constantCoeff (divXPowOrder f * divXPowOrder g) ≠ 0 := by
    rw [map_mul, hf', hg']
    exact mul_ne_zero (fun h => hf (lowestCoeff_eq_zero_iff.1 h))
      (fun h => hg (lowestCoeff_eq_zero_iff.1 h))
  rw [hfg, lowestCoeff_X_pow_mul hc, map_mul, hf', hg']

section Ordered

variable [LinearOrder A] [IsStrictOrderedRing A]

omit [IsStrictOrderedRing A] in
/-- The coefficients of a series with nonnegative lowest coefficient are nonnegative up to its
order. -/
theorem coeff_nonneg_of_le_order {f : A⟦X⟧} (hf : 0 ≤ lowestCoeff f) {k : ℕ}
    (hk : k ≤ f.order.toNat) : 0 ≤ coeff k f := by
  rcases hk.lt_or_eq with hk | hk
  · rw [coeff_of_lt_order_toNat k hk]
  · rw [hk]
    exact hf

theorem lowestCoeff_add_nonneg {f g : A⟦X⟧} (hf : 0 ≤ lowestCoeff f) (hg : 0 ≤ lowestCoeff g) :
    0 ≤ lowestCoeff (f + g) := by
  by_cases hf0 : f = 0
  · rwa [hf0, zero_add]
  by_cases hg0 : g = 0
  · rwa [hg0, add_zero]
  set k := min f.order.toNat g.order.toNat
  have hlow : ∀ i < k, coeff i (f + g) = 0 := fun i hi => by
    rw [map_add, coeff_of_lt_order_toNat i (lt_of_lt_of_le hi (min_le_left _ _)),
      coeff_of_lt_order_toNat i (lt_of_lt_of_le hi (min_le_right _ _)), add_zero]
  have hpos : 0 < coeff k (f + g) := by
    rw [map_add]
    have h1 := coeff_nonneg_of_le_order hf (min_le_left f.order.toNat g.order.toNat)
    have h2 := coeff_nonneg_of_le_order hg (min_le_right f.order.toNat g.order.toNat)
    rcases min_choice f.order.toNat g.order.toNat with hk | hk
    · have : coeff k f ≠ 0 := by rw [show k = f.order.toNat from hk]; exact coeff_order hf0
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne h1 (Ne.symm this)) h2
    · have : coeff k g ≠ 0 := by rw [show k = g.order.toNat from hk]; exact coeff_order hg0
      exact add_pos_of_nonneg_of_pos h1 (lt_of_le_of_ne h2 (Ne.symm this))
  rw [lowestCoeff_eq hpos.ne' hlow]
  exact hpos.le

end Ordered

end PowerSeries

variable (A : Type*) [CommRing A]

/-- `A⟦X⟧` with the lowest-coefficient order. -/
def PowerSeriesLC : Type _ := A⟦X⟧

namespace PowerSeriesLC

instance : CommRing (PowerSeriesLC A) := inferInstanceAs (CommRing A⟦X⟧)

instance : Algebra A (PowerSeriesLC A) := inferInstanceAs (Algebra A A⟦X⟧)

/-- The identification with `A⟦X⟧`. -/
def toPowerSeries : PowerSeriesLC A ≃ₐ[A] A⟦X⟧ := AlgEquiv.refl

variable [LinearOrder A] [IsStrictOrderedRing A]

/-- The cone of series with nonnegative lowest coefficient. -/
def cone : RingCone (PowerSeriesLC A) where
  carrier := {f | 0 ≤ lowestCoeff (toPowerSeries A f)}
  zero_mem' := by simp
  add_mem' {f g} hf hg := lowestCoeff_add_nonneg (f := toPowerSeries A f)
    (g := toPowerSeries A g) hf hg
  one_mem' := by
    change 0 ≤ lowestCoeff (1 : A⟦X⟧)
    rw [lowestCoeff_one]
    exact zero_le_one
  mul_mem' {f g} hf hg := by
    change 0 ≤ lowestCoeff (toPowerSeries A f * toPowerSeries A g)
    rw [lowestCoeff_mul]
    exact mul_nonneg hf hg
  eq_zero_of_mem_of_neg_mem' {f} hf hnf := by
    change 0 ≤ lowestCoeff (-toPowerSeries A f) at hnf
    rw [lowestCoeff_neg] at hnf
    exact lowestCoeff_eq_zero_iff.1 (le_antisymm (neg_nonneg.1 hnf) hf)

theorem mem_cone {f : PowerSeriesLC A} : f ∈ cone A ↔ 0 ≤ lowestCoeff (toPowerSeries A f) :=
  Iff.rfl

instance : HasMemOrNegMem (cone A) where
  mem_or_neg_mem f := by
    rcases le_total 0 (lowestCoeff (toPowerSeries A f)) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change 0 ≤ lowestCoeff (-toPowerSeries A f)
      rw [lowestCoeff_neg]
      exact neg_nonneg.2 h

instance : LinearOrder (PowerSeriesLC A) :=
  open Classical in LinearOrder.mkOfAddGroupCone (cone A)

instance : IsOrderedRing (PowerSeriesLC A) := IsOrderedRing.mkOfCone (cone A)

instance : NoZeroDivisors (PowerSeriesLC A) := inferInstanceAs (NoZeroDivisors A⟦X⟧)

instance : Nontrivial (PowerSeriesLC A) := inferInstanceAs (Nontrivial A⟦X⟧)

instance : IsStrictOrderedRing (PowerSeriesLC A) := IsOrderedRing.toIsStrictOrderedRing _

variable {A}

theorem le_iff {f g : PowerSeriesLC A} :
    f ≤ g ↔ 0 ≤ lowestCoeff (toPowerSeries A g - toPowerSeries A f) := Iff.rfl

end PowerSeriesLC
