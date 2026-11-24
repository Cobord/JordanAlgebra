module

public import JordanDiagram.Algebra.Dyadic
public import JordanDiagram.MathlibMissing.Minkowski
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite groups of `Z[1/2]`-linear automorphisms preserve a finitely generated spanning subgroup

Let `M` be a finitely generated `Z[1/2]`-module and `ρ : G →* GL(M)` a faithful action of a group.
Call an additive subgroup `L ⊆ M` *finitely generated spanning* (`IsFGSpanning`) if it is finitely
generated and `Z[1/2] L = M`, and write `stabilizer ρ L` for the subgroup of `G` preserving `L`.

* `exists_isFGSpanning_le_stabilizer`: **every finite subgroup of `G` preserves a finitely generated
  spanning subgroup**: the sum of the translates of the `ℤ`-span of a finite generating set.
* `card_le_of_le_stabilizer`, `card_le`: when `M` is also free of rank `n`, such an `L` is free of
  rank `n` over `ℤ` (`IsFGSpanning.finrank_eq`), so its stabilizer embeds in `GL_n(ℤ)`; by
  Minkowski's lemma its finite subgroups embed in `GL_n(ℤ/3)`, and **every finite subgroup of `G`
  has order at most `3^(n²)`**.
* `exists_maximal_finite`: so every finite subgroup lies in a maximal finite subgroup.
* `maximal_finite_iff`: if the stabilizer of every finitely generated spanning subgroup is finite,
  **the maximal finite subgroups are the maximal members among these stabilizers**.

For a diagram group, finiteness of these stabilizers comes from discreteness of integer matrices
inside the compact group of real points; it is a hypothesis here.
-/

@[expose] public section

noncomputable section

open Module

namespace ZHalf

variable {M : Type*} [AddCommGroup M] [Module ZHalf M]

/-- The `ℤ`-action on a `Z[1/2]`-module factors through `Z[1/2]` (for the `ℤ`-action on `Z[1/2]`
coming from its algebra structure, which is not reducibly the `zsmul` action). -/
instance isScalarTower_int : @IsScalarTower ℤ ZHalf M Algebra.toSMul _ _ :=
  @IsScalarTower.mk ℤ ZHalf M Algebra.toSMul _ _ fun n r m => by
    rw [Algebra.smul_def, mul_smul, eq_intCast, Int.cast_smul_eq_zsmul]

/-- A finitely generated additive subgroup of a `Z[1/2]`-module that spans it over `Z[1/2]`. -/
structure IsFGSpanning (L : Submodule ℤ M) : Prop where
  fg : L.FG
  span_eq_top : Submodule.span ZHalf (L : Set M) = ⊤

/-- The `Z[1/2]`-linear automorphisms preserving `L`. -/
def stab (L : Submodule ℤ M) : Subgroup (M ≃ₗ[ZHalf] M) where
  carrier := {g | ∀ x, g x ∈ L ↔ x ∈ L}
  mul_mem' {g h} hg hh x := (hg (h x)).trans (hh x)
  one_mem' _ := Iff.rfl
  inv_mem' {g} hg x := by
    have h := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_stab {L : Submodule ℤ M} {g : M ≃ₗ[ZHalf] M} : g ∈ stab L ↔ ∀ x, g x ∈ L ↔ x ∈ L :=
  Iff.rfl

variable {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[ZHalf] M))

/-- The subgroup of `G` preserving `L`. -/
def stabilizer (L : Submodule ℤ M) : Subgroup G := (stab L).comap ρ

theorem mem_stabilizer {L : Submodule ℤ M} {g : G} :
    g ∈ stabilizer ρ L ↔ ∀ x, ρ g x ∈ L ↔ x ∈ L := Iff.rfl

/-! ### Every finite subgroup preserves a finitely generated spanning subgroup -/

/-- An automorphism carrying the generators of `span ℤ s` into it preserves `span ℤ s`. -/
theorem mem_span_of_forall {s : Set M} {g : M ≃ₗ[ZHalf] M} (hg : ∀ y ∈ s, g y ∈ Submodule.span ℤ s)
    {x : M} (hx : x ∈ Submodule.span ℤ s) : g x ∈ Submodule.span ℤ s := by
  have hle : (Submodule.span ℤ s).map (g.toLinearMap.restrictScalars ℤ) ≤ Submodule.span ℤ s :=
    (Submodule.map_span_le _ _ _).2 hg
  exact hle (Submodule.mem_map_of_mem hx)

/-- **Every finite group of automorphisms of a finitely generated `Z[1/2]`-module preserves a
finitely generated spanning subgroup.** -/
theorem exists_isFGSpanning_le_stab [Module.Finite ZHalf M] (K : Subgroup (M ≃ₗ[ZHalf] M))
    [Finite K] : ∃ L : Submodule ℤ M, IsFGSpanning L ∧ K ≤ stab L := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ZHalf) (M := M)
  set gens : Set M := Set.range fun p : K × s => (p.1 : M ≃ₗ[ZHalf] M) p.2
  have hgen : ∀ g ∈ K, ∀ y ∈ gens, g y ∈ Submodule.span ℤ gens := by
    rintro g hg _ ⟨⟨k, t⟩, rfl⟩
    exact Submodule.subset_span ⟨(⟨g, hg⟩ * k, t), rfl⟩
  refine ⟨Submodule.span ℤ gens, ⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff, ← hs, Submodule.span_le]
    intro t ht
    exact Submodule.subset_span (Submodule.subset_span ⟨(1, ⟨t, ht⟩), rfl⟩)
  · intro g hg x
    refine ⟨fun h => ?_, mem_span_of_forall (hgen g hg)⟩
    have := mem_span_of_forall (hgen g⁻¹ (K.inv_mem hg)) h
    rwa [show g⁻¹ (g x) = x from g.symm_apply_apply x] at this

/-- **Every finite subgroup of `G` preserves a finitely generated spanning subgroup.** -/
theorem exists_isFGSpanning_le_stabilizer [Module.Finite ZHalf M] (H : Subgroup G) [Finite H] :
    ∃ L : Submodule ℤ M, IsFGSpanning L ∧ H ≤ stabilizer ρ L := by
  have : Finite (H.map ρ) := Finite.of_surjective
    (fun x : H => (⟨ρ x, Subgroup.mem_map_of_mem ρ x.2⟩ : H.map ρ))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨L, hL, hle⟩ := exists_isFGSpanning_le_stab (H.map ρ)
  exact ⟨L, hL, Subgroup.map_le_iff_le_comap.1 hle⟩

/-! ### A finitely generated spanning subgroup has rank `n` over `ℤ` -/

theorem powers_two_le : Submonoid.powers (2 : ℤ) ≤ nonZeroDivisors ℤ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero

theorem isUnit_algebraMap_powers (s : Submonoid.powers (2 : ℤ)) :
    IsUnit (algebraMap ℤ ZHalf s) :=
  IsLocalization.map_units ZHalf s

/-- `M` is the localization of a finitely generated spanning subgroup at the powers of `2`. -/
theorem IsFGSpanning.isLocalizedModule {L : Submodule ℤ M} (hL : IsFGSpanning L) :
    IsLocalizedModule (Submonoid.powers (2 : ℤ)) L.subtype where
  map_units s := by
    rw [Module.End.isUnit_iff]
    set u := (isUnit_algebraMap_powers s).unit
    have hs : ∀ m : M, (s : ℤ) • m = (u : ZHalf) • m := fun m => by
      rw [IsUnit.unit_spec, algebraMap_smul]
    refine Function.bijective_iff_has_inverse.2 ⟨fun m => (↑u⁻¹ : ZHalf) • m, fun m => ?_,
      fun m => ?_⟩
    · change (↑u⁻¹ : ZHalf) • ((s : ℤ) • m) = m
      rw [hs, smul_smul, Units.inv_mul, one_smul]
    · change (s : ℤ) • ((↑u⁻¹ : ZHalf) • m) = m
      rw [hs, smul_smul, Units.mul_inv, one_smul]
  surj y := by
    have key : ∀ y : M, ∃ k : ℕ, ((2 : ℤ) ^ k) • y ∈ L := by
      let P : Submodule ZHalf M :=
        { carrier := {y | ∃ k : ℕ, ((2 : ℤ) ^ k) • y ∈ L}
          add_mem' := by
            rintro y z ⟨k, hk⟩ ⟨l, hl⟩
            refine ⟨k + l, ?_⟩
            rw [smul_add, pow_add]
            refine L.add_mem ?_ ?_
            · rw [mul_comm, mul_smul]
              exact L.smul_mem _ hk
            · rw [mul_smul]
              exact L.smul_mem _ hl
          zero_mem' := ⟨0, by simp⟩
          smul_mem' := by
            rintro r y ⟨k, hk⟩
            obtain ⟨⟨n, s⟩, hr⟩ := IsLocalization.surj (Submonoid.powers (2 : ℤ)) r
            obtain ⟨j, hj⟩ := s.2
            have hj : (2 : ℤ) ^ j = s := hj
            refine ⟨j + k, ?_⟩
            change ((2 : ℤ) ^ (j + k)) • (r • y) ∈ L
            have : ((2 : ℤ) ^ (j + k)) • (r • y) = n • ((2 : ℤ) ^ k • y) := by
              calc ((2 : ℤ) ^ (j + k)) • (r • y)
                  = (algebraMap ℤ ZHalf ((2 : ℤ) ^ (j + k)) * r) • y := by
                    rw [mul_smul, algebraMap_smul]
                _ = (algebraMap ℤ ZHalf n * algebraMap ℤ ZHalf ((2 : ℤ) ^ k)) • y := by
                    rw [pow_add, map_mul, hj, ← hr]
                    ring_nf
                _ = n • ((2 : ℤ) ^ k • y) := by
                    rw [mul_smul, algebraMap_smul, algebraMap_smul]
            rw [this]
            exact L.smul_mem _ hk }
      have hP : P = ⊤ := by
        rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
        exact fun y hy => ⟨0, by simpa using hy⟩
      intro y
      have : y ∈ P := hP ▸ Submodule.mem_top
      exact this
    obtain ⟨k, hk⟩ := key y
    exact ⟨(⟨_, hk⟩, ⟨2 ^ k, k, rfl⟩), rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

/-- A `Z[1/2]`-module that is free is torsion-free over `ℤ`. -/
theorem isTorsionFree_int [Module.Free ZHalf M] : Module.IsTorsionFree ℤ M := by
  have h := (faithfulSMul_iff_algebraMap_injective ℤ ZHalf).2
    (IsLocalization.injective ZHalf powers_two_le)
  exact .trans_faithfulSMul ℤ ZHalf M

/-- A finitely generated spanning subgroup of a free `Z[1/2]`-module is free over `ℤ`. -/
theorem IsFGSpanning.free {L : Submodule ℤ M} [Module.Free ZHalf M] (hL : IsFGSpanning L) :
    Module.Free ℤ L := by
  have := isTorsionFree_int (M := M)
  have : Module.IsTorsionFree ℤ L :=
    Subtype.val_injective.moduleIsTorsionFree _ fun _ _ => rfl
  have : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL.fg
  infer_instance

/-- **A finitely generated spanning subgroup has the same rank over `ℤ` as `M` over `Z[1/2]`.** -/
theorem IsFGSpanning.finrank_eq {L : Submodule ℤ M} [Module.Free ZHalf M] (hL : IsFGSpanning L) :
    finrank ℤ L = finrank ZHalf M := by
  have := hL.isLocalizedModule
  rw [IsLocalization.finrank_eq ZHalf (Submonoid.powers (2 : ℤ)) powers_two_le,
    IsLocalizedModule.finrank_eq (Submonoid.powers (2 : ℤ)) L.subtype powers_two_le]

/-! ### The stabilizer of a finitely generated spanning subgroup embeds in `GL_n(ℤ)` -/

/-- The restriction of an automorphism preserving `L` to `L`. -/
def restrictEnd (L : Submodule ℤ M) : stab L →* Module.End ℤ L where
  toFun g := (g.1.toLinearMap.restrictScalars ℤ).restrict fun x hx => (g.2 x).2 hx
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrictEnd_injective {L : Submodule ℤ M} (hL : IsFGSpanning L) :
    Function.Injective (restrictEnd L) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hL.span_eq_top fun x hx => ?_
  have := congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)
  exact this

/-- The embedding of the stabilizer of `L` into `GL_n(ℤ)` given by a `ℤ`-basis of `L`. -/
def toGL {L : Submodule ℤ M} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    stab L →* GL ι ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp
    (restrictEnd L).toHomUnits

theorem toGL_injective {L : Submodule ℤ M} (hL : IsFGSpanning L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ L) : Function.Injective (toGL b) := by
  intro g h hgh
  apply restrictEnd_injective hL
  have := congrArg (fun u : GL ι ℤ => (u : Matrix ι ι ℤ)) hgh
  exact (LinearMap.toMatrixAlgEquiv b).injective this

/-- `|GL_n(ℤ/3)| ≤ 3^(n²)`. -/
theorem card_GL_zmod_three_le (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Nat.card (GL ι (ZMod 3)) ≤ 3 ^ (Fintype.card ι * Fintype.card ι) := by
  have hle : Nat.card (GL ι (ZMod 3)) ≤ Nat.card (Matrix ι ι (ZMod 3)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  refine hle.trans (le_of_eq ?_)
  change Nat.card (ι → ι → ZMod 3) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, ← pow_mul]

/-- A finite subgroup of a group embedding in `GL_n(ℤ)` has order at most `3^(n²)`. -/
theorem card_le_of_injective_GL {G' : Type*} [Group G'] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : G' →* GL ι ℤ} (hψ : Function.Injective ψ) (H : Subgroup G') [Finite H] :
    Nat.card H ≤ 3 ^ (Fintype.card ι * Fintype.card ι) := by
  have : Finite (H.map ψ) := Finite.of_surjective _ (H.equivMapOfInjective ψ hψ).surjective
  have hinj := Matrix.injOn_reduce (n := ι) (m := 3) le_rfl (H.map ψ)
  have h1 : Nat.card (H.map ψ) ≤ Nat.card (GL ι (ZMod 3)) :=
    Nat.card_le_card_of_injective (fun x => Matrix.reduce 3 (x : GL ι ℤ))
      fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  rw [← Subgroup.card_map_of_injective hψ]
  exact h1.trans (card_GL_zmod_three_le ι)

variable {ρ}

/-- **A finite subgroup preserving a finitely generated spanning subgroup has order at most
`3^(n²)`**, `n` the rank of `M`. -/
theorem card_le_of_le_stabilizer [Module.Free ZHalf M] (hρ : Function.Injective ρ)
    {L : Submodule ℤ M} (hL : IsFGSpanning L) (H : Subgroup G) [Finite H]
    (hH : H ≤ stabilizer ρ L) :
    Nat.card H ≤ 3 ^ (finrank ZHalf M * finrank ZHalf M) := by
  classical
  have := hL.free
  have : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL.fg
  set b := Module.Free.chooseBasis ℤ L
  let ψ : stabilizer ρ L →* GL _ ℤ := (toGL b).comp (ρ.subgroupComap (stab L))
  have hψ : Function.Injective ψ := (toGL_injective hL b).comp fun x y hxy =>
    Subtype.ext (hρ (congrArg Subtype.val hxy))
  have : Finite (H.subgroupOf (stabilizer ρ L)) :=
    Finite.of_injective _ (Subgroup.subgroupOfEquivOfLe hH).injective
  have h := card_le_of_injective_GL hψ (H.subgroupOf (stabilizer ρ L))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv,
    ← Module.finrank_eq_card_chooseBasisIndex, hL.finrank_eq] at h

/-- **The finite subgroups of `G` have order at most `3^(n²)`**, `n` the rank of `M`. -/
theorem card_le [Module.Free ZHalf M] [Module.Finite ZHalf M] (hρ : Function.Injective ρ)
    (H : Subgroup G) [Finite H] : Nat.card H ≤ 3 ^ (finrank ZHalf M * finrank ZHalf M) := by
  obtain ⟨L, hL, hle⟩ := exists_isFGSpanning_le_stabilizer ρ H
  exact card_le_of_le_stabilizer hρ hL H hle

/-! ### Maximal finite subgroups -/

/-- **Every finite subgroup lies in a maximal finite subgroup.** -/
theorem exists_maximal_finite [Module.Free ZHalf M] [Module.Finite ZHalf M]
    (hρ : Function.Injective ρ) (H : Subgroup G) [Finite H] :
    ∃ K : Subgroup G, H ≤ K ∧ Maximal (fun K : Subgroup G => Finite K) K := by
  set B := 3 ^ (finrank ZHalf M * finrank ZHalf M)
  set S : Set ℕ := {n | ∃ K : Subgroup G, H ≤ K ∧ Finite K ∧ Nat.card K = n}
  have hS : BddAbove S := ⟨B, by
    rintro _ ⟨K, -, hK, rfl⟩
    exact card_le hρ K⟩
  have hne : S.Nonempty := ⟨_, H, le_rfl, inferInstance, rfl⟩
  obtain ⟨K, hHK, hK, hcard⟩ := Nat.sSup_mem hne hS
  refine ⟨K, hHK, hK, fun K' hK' hle => ?_⟩
  have : Nat.card K' ≤ Nat.card K := hcard ▸ le_csSup hS ⟨K', hHK.trans hle, hK', rfl⟩
  exact (Subgroup.eq_of_le_of_card_ge hle this).ge

/-- **If the stabilizer of every finitely generated spanning subgroup is finite, the maximal finite
subgroups are the maximal members among these stabilizers.** -/
theorem maximal_finite_iff [Module.Finite ZHalf M]
    (hfin : ∀ L : Submodule ℤ M, IsFGSpanning L → Finite (stabilizer ρ L)) (K : Subgroup G) :
    Maximal (fun K : Subgroup G => Finite K) K ↔
      Maximal (fun K : Subgroup G => ∃ L, IsFGSpanning L ∧ K = stabilizer ρ L) K := by
  constructor
  · rintro ⟨hK, hmax⟩
    obtain ⟨L, hL, hle⟩ := exists_isFGSpanning_le_stabilizer ρ K
    have := hfin L hL
    have hKL : K = stabilizer ρ L := le_antisymm hle (hmax this hle)
    refine ⟨⟨L, hL, hKL⟩, ?_⟩
    rintro _ ⟨L', hL', rfl⟩ hle'
    exact hmax (hfin L' hL') hle'
  · rintro ⟨⟨L, hL, rfl⟩, hmax⟩
    refine ⟨hfin L hL, fun K' hK' hle => ?_⟩
    obtain ⟨L', hL', hle'⟩ := exists_isFGSpanning_le_stabilizer ρ K'
    exact hle'.trans (hmax ⟨L', hL', rfl⟩ (hle.trans hle'))

end ZHalf
