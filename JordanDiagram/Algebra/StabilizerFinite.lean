module

public import JordanDiagram.Algebra.FiniteSubgroupStabilizer
public import JordanDiagram.MathlibMissing.PosDefIntegerPoints

/-!
# Stabilizers are finite in the presence of an invariant positive form

Let `M` be a finite free `Z[1/2]`-module, `ρ : G →* GL(M)` a faithful action, and `β` a
biadditive `ℚ`-valued form on `M` invariant under `G` with `β(x, x) > 0` for `x ≠ 0` (e.g. the
trace form of a formally real Jordan algebra over `Z[1/2]`). Then the stabilizer of every finitely
generated spanning subgroup `L ⊆ M` is finite (`finite_stabilizer_of_form`): in a `ℤ`-basis of `L`
an element of the stabilizer is an integer matrix whose columns `w` satisfy `wᵀ A w = A_jj` for the
Gram matrix `A` of `β`, and there are finitely many such integer vectors
(`Matrix.finite_setOf_int_le`). This discharges the hypothesis of `maximal_finite_iff`
(`maximal_finite_iff_of_form`).
-/

@[expose] public section

noncomputable section

open Module Matrix

namespace ZHalf

variable {M : Type*} [AddCommGroup M] [Module ZHalf M]
variable {G : Type*} [Group G] {ρ : G →* (M ≃ₗ[ZHalf] M)}

omit [Module ZHalf M] in
/-- The value of a biadditive form on an element given by integer coordinates in a family. -/
theorem form_sum_zsmul (β : M →+ M →+ ℚ) {ι : Type*} [Fintype ι] (x : ι → M) (c : ι → ℤ) :
    β (∑ i, c i • x i) (∑ i, c i • x i) =
      (fun i => (c i : ℚ)) ⬝ᵥ (Matrix.of fun i j => β (x i) (x j)) *ᵥ fun i => (c i : ℚ) := by
  simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_smul,
    Pi.smul_apply, zsmul_eq_mul, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Finite stabilizers**: under an invariant form `β` with `β(x, x) > 0` for `x ≠ 0`, the
stabilizer of every finitely generated spanning subgroup is finite. -/
theorem finite_stabilizer_of_form [Module.Free ZHalf M] (hρ : Function.Injective ρ)
    (β : M →+ M →+ ℚ) (hpos : ∀ x, x ≠ 0 → 0 < β x x)
    (hinv : ∀ g x y, β (ρ g x) (ρ g y) = β x y) {L : Submodule ℤ M} (hL : IsFGSpanning L) :
    Finite (stabilizer ρ L) := by
  classical
  have := hL.free
  have : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL.fg
  set b := Module.Free.chooseBasis ℤ L
  set ι := Module.Free.ChooseBasisIndex ℤ L
  set A : Matrix ι ι ℚ := Matrix.of fun i j => β (b i) (b j)
  -- the form in coordinates
  have hcoord : ∀ y : L, β y y =
      (fun i => (b.repr y i : ℚ)) ⬝ᵥ A *ᵥ fun i => (b.repr y i : ℚ) := fun y => by
    have hy : (y : M) = ∑ i, b.repr y i • (b i : M) := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Submodule.coe_sum]
      rfl
    rw [hy, form_sum_zsmul]
  have hA : ∀ w : ι → ℤ, w ≠ 0 → 0 < (fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ fun i => (w i : ℚ) := by
    intro w hw
    set y : L := b.equivFun.symm w
    have hrepr : ∀ i, b.repr y i = w i := fun i => by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hy : (y : M) ≠ 0 := by
      intro h
      apply hw
      funext i
      rw [← hrepr i, Submodule.coe_eq_zero.1 h, map_zero, Finsupp.zero_apply, Pi.zero_apply]
    have := hcoord y
    simp only [hrepr] at this
    rw [← this]
    exact hpos _ hy
  -- columns of an element of the stabilizer
  have hmem : ∀ g ∈ stabilizer ρ L, ∀ j, ρ g (b j) ∈ L := fun g hg j =>
    ((mem_stabilizer ρ).1 hg _).2 (b j).2
  let col : stabilizer ρ L → ι → ι → ℤ := fun g j i => b.repr ⟨ρ g.1 (b j), hmem g.1 g.2 j⟩ i
  set S : Set (ι → ι → ℤ) := Set.pi Set.univ fun j =>
    {w : ι → ℤ | (fun i => (w i : ℚ)) ⬝ᵥ A *ᵥ (fun i => (w i : ℚ)) ≤ A j j}
  have hS : S.Finite := Set.Finite.pi fun j => Matrix.finite_setOf_int_le A hA _
  have hcolS : ∀ g, col g ∈ S := fun g j _ => by
    have := hcoord ⟨ρ g.1 (b j), hmem g.1 g.2 j⟩
    simp only [Set.mem_ofPred_eq]
    rw [← this]
    exact (hinv g.1 _ _).le
  have hinj : Function.Injective col := by
    intro g h hgh
    apply Subtype.ext
    apply hρ
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext_on hL.span_eq_top fun x hx => ?_
    have hb : ∀ j, ρ g.1 (b j) = ρ h.1 (b j) := fun j =>
      congrArg Subtype.val
        (b.repr.injective (Finsupp.ext fun i => congrFun (congrFun hgh j) i))
    have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : M) := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : L) : M) from rfl, ← b.sum_repr ⟨x, hx⟩]
      rw [Submodule.coe_sum]
      rfl
    change ρ g.1 x = ρ h.1 x
    rw [hx', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_zsmul, hb]
  have := hS.to_subtype
  exact Finite.of_injective (fun g => (⟨col g, hcolS g⟩ : S)) fun g h hgh =>
    hinj (congrArg Subtype.val hgh)

/-- **Maximal finite subgroups under an invariant positive form**: the maximal finite subgroups
are the maximal members among the stabilizers of finitely generated spanning subgroups. -/
theorem maximal_finite_iff_of_form [Module.Free ZHalf M] [Module.Finite ZHalf M]
    (hρ : Function.Injective ρ) (β : M →+ M →+ ℚ) (hpos : ∀ x, x ≠ 0 → 0 < β x x)
    (hinv : ∀ g x y, β (ρ g x) (ρ g y) = β x y) (K : Subgroup G) :
    Maximal (fun K : Subgroup G => Finite K) K ↔
      Maximal (fun K : Subgroup G => ∃ L, IsFGSpanning L ∧ K = stabilizer ρ L) K :=
  maximal_finite_iff (fun _ hL => finite_stabilizer_of_form hρ β hpos hinv hL) K

end ZHalf
