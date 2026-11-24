module

public import JordanDiagram.Diagram.Ordered
public import JordanDiagram.Diagram.PowerSeries
public import JordanDiagram.MathlibMissing.PowerSeriesOrder
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Power series as an ordered scalar object

Let `A` be a totally ordered commutative ring (for instance `Z[1/2]`), and give `A⟦t⟧` the
lowest-coefficient order (`PowerSeriesLC A`), in which `0 < t < a` for every `a > 0`
(`PowerSeriesLC.t_pos`, `PowerSeriesLC.t_lt_C`).

* `PowerSeriesLC.ordScalar A`: `A⟦t⟧` is an object of the ordered scalar category over `A`, as is
  `A` itself (`OrdScalar.base A`).
* `PowerSeriesLC.constTermHom`: **the constant-term map `A⟦t⟧ → A` is a morphism** of ordered
  scalars. It is order-preserving, and continuous because it is locally constant: it is constant
  on every interval `(f - t, f + t)`.
* `PowerSeriesLC.not_continuous_algebraMap`: **the constant-series inclusion `A → A⟦t⟧` is not
  continuous** when `2` is invertible in `A`, since `(-t, t)` pulls back to `{0}`. As it is the
  only `A`-algebra map, there is no morphism `A ⟶ A⟦t⟧` (`PowerSeriesLC.isEmpty_hom`): `A` is an
  object but not an initial object of the ordered scalar category.
-/

@[expose] public section

universe u

open PowerSeries Topology CategoryTheory

namespace JordanDiagram

noncomputable section

namespace PowerSeriesLC

variable {A : Type u} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]

/-- The variable `t` of `A⟦t⟧`. -/
def t : PowerSeriesLC A := (PowerSeriesLC.toPowerSeries A).symm X

/-- The constant term of a series. -/
def constTerm (f : PowerSeriesLC A) : A := constantCoeff (PowerSeriesLC.toPowerSeries A f)

omit [LinearOrder A] [IsStrictOrderedRing A] in
theorem toPowerSeries_t : PowerSeriesLC.toPowerSeries A t = X :=
  (PowerSeriesLC.toPowerSeries A).apply_symm_apply X

omit [LinearOrder A] [IsStrictOrderedRing A] in
theorem toPowerSeries_algebraMap (a : A) :
    PowerSeriesLC.toPowerSeries A (algebraMap A (PowerSeriesLC A) a) = C a :=
  (PowerSeriesLC.toPowerSeries A).commutes a |>.trans PowerSeries.algebraMap_apply

omit [LinearOrder A] [IsStrictOrderedRing A] in
theorem lowestCoeff_of_constantCoeff_ne_zero {f : A⟦X⟧} (hf : constantCoeff f ≠ 0) :
    lowestCoeff f = constantCoeff f := by
  rw [lowestCoeff_eq (n := 0) (by rwa [coeff_zero_eq_constantCoeff_apply])
    (fun i hi => absurd hi (Nat.not_lt_zero i)), coeff_zero_eq_constantCoeff_apply]

theorem lowestCoeff_X : lowestCoeff (X : A⟦X⟧) = 1 := by
  have := lowestCoeff_X_pow_mul (h := (1 : A⟦X⟧)) (by simp) 1
  rwa [pow_one, mul_one, map_one] at this

/-- `t` is positive. -/
theorem t_pos : (0 : PowerSeriesLC A) < t := by
  refine lt_of_le_of_ne ?_ fun h => X_ne_zero (R := A) ?_
  · rw [PowerSeriesLC.le_iff, map_zero, sub_zero, toPowerSeries_t, lowestCoeff_X]
    exact zero_le_one
  · rw [← toPowerSeries_t, ← h, map_zero]

/-- `t` is infinitesimal: below every positive constant. -/
theorem t_lt_C {a : A} (ha : 0 < a) : t < algebraMap A (PowerSeriesLC A) a := by
  have hc : constantCoeff (C a - X : A⟦X⟧) = a := by simp
  refine lt_of_le_of_ne ?_ fun h => ?_
  · rw [PowerSeriesLC.le_iff, toPowerSeries_algebraMap, toPowerSeries_t,
      lowestCoeff_of_constantCoeff_ne_zero (by rw [hc]; exact ha.ne'), hc]
    exact ha.le
  · have := congrArg (fun f => constantCoeff (PowerSeriesLC.toPowerSeries A f)) h
    simp only [toPowerSeries_t, toPowerSeries_algebraMap, constantCoeff_X, constantCoeff_C] at this
    exact ha.ne' this.symm

/-- A series strictly between `-t` and `t` has constant term `0`. -/
theorem constTerm_eq_zero {h : PowerSeriesLC A} (h1 : -t < h) (h2 : h < t) : constTerm h = 0 := by
  by_contra hc
  have hc' : constantCoeff (PowerSeriesLC.toPowerSeries A h) ≠ 0 := hc
  have hle2 := PowerSeriesLC.le_iff.1 h2.le
  have hle1 := PowerSeriesLC.le_iff.1 h1.le
  rw [toPowerSeries_t] at hle2
  rw [map_neg, toPowerSeries_t, sub_neg_eq_add] at hle1
  have e2 : constantCoeff (X - PowerSeriesLC.toPowerSeries A h) =
      -constantCoeff (PowerSeriesLC.toPowerSeries A h) := by simp
  have e1 : constantCoeff (PowerSeriesLC.toPowerSeries A h + X) =
      constantCoeff (PowerSeriesLC.toPowerSeries A h) := by simp
  rw [lowestCoeff_of_constantCoeff_ne_zero (by rw [e2]; exact neg_ne_zero.2 hc'), e2] at hle2
  rw [lowestCoeff_of_constantCoeff_ne_zero (by rw [e1]; exact hc'), e1] at hle1
  exact hc' (le_antisymm (neg_nonneg.1 hle2) hle1)

omit [LinearOrder A] [IsStrictOrderedRing A] in
theorem constTerm_sub (f g : PowerSeriesLC A) : constTerm (f - g) = constTerm f - constTerm g := by
  simp [constTerm]

omit [LinearOrder A] [IsStrictOrderedRing A] in
theorem constTerm_algebraMap (a : A) : constTerm (algebraMap A (PowerSeriesLC A) a) = a := by
  rw [constTerm, toPowerSeries_algebraMap, constantCoeff_C]

/-- The constant term is order-preserving. -/
theorem constTerm_monotone : Monotone (constTerm (A := A)) := fun f g hfg => by
  have := coeff_nonneg_of_le_order (PowerSeriesLC.le_iff.1 hfg) (Nat.zero_le _)
  rw [coeff_zero_eq_constantCoeff_apply, map_sub] at this
  exact sub_nonneg.1 this

/-- The constant term is locally constant for the order topology, hence continuous. -/
theorem constTerm_continuous :
    @Continuous (PowerSeriesLC A) A (Preorder.topology _) (Preorder.topology A) constTerm := by
  let _ : TopologicalSpace (PowerSeriesLC A) := Preorder.topology _
  let _ : TopologicalSpace A := Preorder.topology A
  have _ : OrderTopology (PowerSeriesLC A) := ⟨rfl⟩
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun f => ?_)
  filter_upwards [Ioo_mem_nhds (sub_lt_self f t_pos) (lt_add_of_pos_right f t_pos)] with g hg
  have h0 : constTerm (g - f) = 0 :=
    constTerm_eq_zero (by linarith [hg.1]) (by linarith [hg.2])
  rw [constTerm_sub, sub_eq_zero] at h0
  exact h0

variable (A) in
/-- `A⟦t⟧` with the lowest-coefficient order, as an ordered scalar object over `A`. -/
abbrev ordScalar : OrdScalar.{u, u} A where
  carrier := PowerSeriesLC A
  monotone_algebraMap a b hab := by
    rw [PowerSeriesLC.le_iff, toPowerSeries_algebraMap, toPowerSeries_algebraMap, ← map_sub,
      lowestCoeff_C]
    exact sub_nonneg.2 hab

variable (A) in
/-- `A` itself as an ordered scalar object over `A`. -/
abbrev baseObj : OrdScalar.{u, u} A where
  carrier := A
  monotone_algebraMap := monotone_id

/-- **The constant-term map `A⟦t⟧ → A` is a morphism of ordered scalars.** -/
def constTermHom : ordScalar A ⟶ baseObj A :=
  ⟨(constCoeffAlg (R := A) A).comp (PowerSeriesLC.toPowerSeries A).toAlgHom,
    constTerm_monotone, constTerm_continuous⟩

theorem constTermHom_hom (f : PowerSeriesLC A) : (constTermHom (A := A)).hom f = constTerm f :=
  rfl

/-- **The constant-series inclusion `A → A⟦t⟧` is not continuous** for the order topologies. -/
theorem not_continuous_algebraMap [Invertible (2 : A)] :
    ¬ @Continuous A (PowerSeriesLC A) (Preorder.topology A) (Preorder.topology _)
      (algebraMap A (PowerSeriesLC A)) := by
  intro hc
  let _ : TopologicalSpace (PowerSeriesLC A) := Preorder.topology _
  let _ : TopologicalSpace A := Preorder.topology A
  have _ : OrderTopology A := ⟨rfl⟩
  have _ : OrderTopology (PowerSeriesLC A) := ⟨rfl⟩
  have hopen : IsOpen (algebraMap A (PowerSeriesLC A) ⁻¹' Set.Ioo (-t) t) :=
    isOpen_Ioo.preimage hc
  have h0 : (0 : A) ∈ algebraMap A (PowerSeriesLC A) ⁻¹' Set.Ioo (-t) t := by
    simp only [Set.mem_preimage, map_zero, Set.mem_Ioo, neg_lt_zero]
    exact ⟨t_pos, t_pos⟩
  obtain ⟨l, v, ⟨hl, hv⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds h0)
  obtain ⟨hr0, hrv⟩ := mul_invOf_two_mem_Ioo hv
  have hmem := hsub ⟨lt_trans hl hr0, hrv⟩
  have := constTerm_eq_zero hmem.1 hmem.2
  rw [constTerm_algebraMap] at this
  exact hr0.ne' this

/-- **`A` is not initial among ordered scalars**: there is no morphism `A ⟶ A⟦t⟧`, the only
`A`-algebra map being the discontinuous constant-series inclusion. -/
theorem isEmpty_hom [Invertible (2 : A)] : IsEmpty (baseObj A ⟶ ordScalar A) :=
  ⟨fun f => not_continuous_algebraMap (by
    have : (f.hom : A → PowerSeriesLC A) = algebraMap A (PowerSeriesLC A) :=
      funext fun a => f.hom.commutes a
    rw [← this]
    exact f.continuous)⟩

end PowerSeriesLC

end

end JordanDiagram
