module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# The ordered fraction field of a totally ordered ring

Let `R` be a totally ordered commutative ring (`IsStrictOrderedRing`). It is an integral domain
(`IsStrictOrderedRing.isDomain`), and its fraction field `K = FractionRing R` carries a unique order
extending that of `R`: `a / b ≥ 0` exactly when `a b ≥ 0`.

* `FractionRing.posCone`: the cone `{a / b | a b ≥ 0}`; it gives `K` a `LinearOrder` and makes it
  an `IsStrictOrderedRing`.
* `FractionRing.algebraMap_le_iff`: the order extends that of `R`.
* `FractionRing.le_iff_of_order`: **uniqueness**: any order on `K` making it a totally ordered
  ring in which `R → K` is order-preserving is this one.
-/

@[expose] public section

noncomputable section

/-- In a totally ordered field, `0 ≤ p / q ↔ 0 ≤ p q` for `q ≠ 0`. -/
theorem div_nonneg_iff_mul_nonneg {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {p q : F} (hq : q ≠ 0) : 0 ≤ p / q ↔ 0 ≤ p * q := by
  have hqq : 0 < q * q := mul_self_pos.2 hq
  have e : p / q = p * q / (q * q) := by field_simp
  rw [e]
  refine ⟨fun h => ?_, fun h => div_nonneg h hqq.le⟩
  have := mul_nonneg h hqq.le
  rwa [div_mul_cancel₀ _ hqq.ne'] at this

namespace FractionRing

variable (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem algebraMap_ne_zero [IsDomain R] {b : R} (hb : b ≠ 0) : algebraMap R (FractionRing R) b ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb

theorem exists_eq_div (x : FractionRing R) :
    ∃ a b : R, b ≠ 0 ∧ x = algebraMap R _ a / algebraMap R _ b := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  exact ⟨a, b, nonZeroDivisors.ne_zero hb, rfl⟩

/-- The positive cone `{a / b | a b ≥ 0}` of the fraction field. -/
def posCone : RingCone (FractionRing R) where
  carrier := {x | ∃ a b : R, b ≠ 0 ∧ x = algebraMap R _ a / algebraMap R _ b ∧ 0 ≤ a * b}
  zero_mem' := ⟨0, 1, one_ne_zero, by simp, by simp⟩
  one_mem' := ⟨1, 1, one_ne_zero, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, rfl, hcd⟩
    refine ⟨a * d + b * c, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · rw [div_add_div _ _ (algebraMap_ne_zero R hb) (algebraMap_ne_zero R hd)]
      simp only [map_add, map_mul]
    · nlinarith [mul_nonneg hab (mul_self_nonneg d), mul_nonneg hcd (mul_self_nonneg b)]
  mul_mem' := by
    rintro x y ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, rfl, hcd⟩
    refine ⟨a * c, b * d, mul_ne_zero hb hd, by rw [div_mul_div_comm, map_mul, map_mul], ?_⟩
    nlinarith [mul_nonneg hab hcd]
  eq_zero_of_mem_of_neg_mem' := by
    rintro x ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, hx, hcd⟩
    have hb' := algebraMap_ne_zero R hb
    have hd' := algebraMap_ne_zero R hd
    have hcross : -(a * d) = c * b := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [← neg_div, div_eq_div_iff hb' hd'] at hx
      rw [map_neg, map_mul, map_mul, ← hx, neg_mul]
    have h1 : 0 ≤ a * b * (d * d) := mul_nonneg hab (mul_self_nonneg d)
    have h2 : 0 ≤ c * d * (b * b) := mul_nonneg hcd (mul_self_nonneg b)
    have h3 : c * d * (b * b) = -(a * b * (d * d)) := by linear_combination (d * b) * hcross.symm
    have h4 : a * b * (d * d) = 0 := by linarith
    have ha : a = 0 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact (mul_eq_zero.1 h).resolve_right hb
      · exact absurd (mul_self_eq_zero.1 h) hd
    rw [ha, map_zero, zero_div]

theorem mem_posCone {x : FractionRing R} :
    x ∈ posCone R ↔ ∃ a b : R, b ≠ 0 ∧ x = algebraMap R _ a / algebraMap R _ b ∧ 0 ≤ a * b :=
  Iff.rfl

instance : HasMemOrNegMem (posCone R) where
  mem_or_neg_mem x := by
    obtain ⟨a, b, hb, rfl⟩ := exists_eq_div R x
    rcases le_total 0 (a * b) with h | h
    · exact Or.inl ⟨a, b, hb, rfl, h⟩
    · exact Or.inr ⟨-a, b, hb, by rw [map_neg]; exact (neg_div _ _).symm,
        by rw [neg_mul]; exact neg_nonneg.2 h⟩

instance : LinearOrder (FractionRing R) :=
  open Classical in LinearOrder.mkOfAddGroupCone (posCone R)

instance : IsOrderedRing (FractionRing R) := IsOrderedRing.mkOfCone (posCone R)

instance : IsStrictOrderedRing (FractionRing R) := IsOrderedRing.toIsStrictOrderedRing _

variable {R}

theorem le_iff {x y : FractionRing R} : x ≤ y ↔ y - x ∈ posCone R := Iff.rfl

/-- **The order of the fraction field extends that of `R`.** -/
theorem algebraMap_le_iff {r s : R} :
    algebraMap R (FractionRing R) r ≤ algebraMap R (FractionRing R) s ↔ r ≤ s := by
  rw [le_iff, ← map_sub]
  constructor
  · rintro ⟨a, b, hb, he, hab⟩
    rw [eq_div_iff (algebraMap_ne_zero R hb), ← map_mul] at he
    have he' := IsFractionRing.injective R (FractionRing R) he
    have : 0 ≤ (s - r) * (b * b) := by rw [← mul_assoc, he']; exact hab
    exact sub_nonneg.1 (le_of_mul_le_mul_right (by rw [zero_mul]; exact this)
      (mul_self_pos.2 hb))
  · intro h
    exact ⟨s - r, 1, one_ne_zero, by simp, by simpa using h⟩

/-- **Uniqueness of the order**: any order on `K` making it a totally ordered ring in which
`R → K` is order-preserving coincides with the order of `posCone`, which is the order of `K`
(`le_iff`). -/
theorem le_iff_of_order (o : LinearOrder (FractionRing R))
    (ho : @IsStrictOrderedRing (FractionRing R) _ o.toPartialOrder)
    (hmono : ∀ r s : R, r ≤ s → o.le (algebraMap R _ r) (algebraMap R _ s)) (x y : FractionRing R) :
    o.le x y ↔ y - x ∈ posCone R := by
  have key : ∀ z : FractionRing R, o.le 0 z ↔ z ∈ posCone R := by
    intro z
    let _ := o
    -- `R → K` reflects the order
    have hrefl : ∀ c : R, o.le 0 (algebraMap R _ c) → 0 ≤ c := fun c hc => by
      by_contra hneg
      push Not at hneg
      have h1 := hmono c 0 hneg.le
      rw [map_zero] at h1
      have h2 : algebraMap R (FractionRing R) c = 0 := le_antisymm h1 hc
      exact hneg.ne ((map_eq_zero_iff _ (IsFractionRing.injective R _)).1 h2)
    constructor
    · intro hz
      obtain ⟨a, b, hb, rfl⟩ := exists_eq_div R z
      refine ⟨a, b, hb, rfl, hrefl _ ?_⟩
      rw [map_mul]
      exact (@div_nonneg_iff_mul_nonneg _ _ o ho _ _ (algebraMap_ne_zero R hb)).1 hz
    · rintro ⟨a, b, hb, rfl, hab⟩
      refine (@div_nonneg_iff_mul_nonneg _ _ o ho _ _ (algebraMap_ne_zero R hb)).2 ?_
      have := hmono 0 (a * b) hab
      rwa [map_zero, map_mul] at this
  have hsub : o.le x y ↔ o.le 0 (y - x) := by
    let _ := o
    have _ := ho
    exact sub_nonneg.symm
  exact hsub.trans (key _)

end FractionRing
