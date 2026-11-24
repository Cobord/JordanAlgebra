module

public import JordanDiagram.Diagram.Group
public import JordanDiagram.Algebra.FiniteSubgroupStabilizer

/-!
# Finite subgroups of a diagram group

For a diagram `F` over `Z[1/2]` with finitely many objects and finite free nodes, `G_F(Z[1/2])`
acts faithfully on `M = ∏ᵢ F(i)` (`nodesRep`), and also on the terminal algebra `F(+)` when the
terminal maps are injective (`terminalRep`). The results of
`Algebra/FiniteSubgroupStabilizer.lean` apply to either action (`finite_subgroups_nodes`,
`finite_subgroups_terminal`):

* every finite subgroup preserves a finitely generated additive subgroup `L ⊆ M` with
  `Z[1/2] L = M`;
* the orders of finite subgroups are bounded (by `3^(n²)`, `n` the rank of `M`), so every finite
  subgroup lies in a maximal finite subgroup;
* if the stabilizer of every such `L` is finite (as when the real points form a compact group), the
  maximal finite subgroups are the maximal members among these stabilizers.
-/

@[expose] public section

universe v w w'

open CategoryTheory TerminallyPointed JordanAlgebra Module ZHalf

namespace JordanDiagram

variable {I : Type w} [Category.{w'} I] [TerminallyPointed I] (F : JordanDiagram.{0, v} ZHalf I)

/-- `G_F(Z[1/2])` acting on the product of all the nodes. -/
def nodesRep : F.autGroup →* ((∀ i, F.obj i) ≃ₗ[ZHalf] (∀ i, F.obj i)) where
  toFun g := LinearEquiv.piCongrRight fun i => (g.1 i : F.obj i ≃ₗ[ZHalf] F.obj i)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

omit [TerminallyPointed I] in
theorem nodesRep_injective : Function.Injective F.nodesRep := by
  classical
  intro g h hgh
  refine Subtype.ext (funext fun i => jordanAut.ext fun x => ?_)
  have := congrArg (fun e : (∀ i, F.obj i) ≃ₗ[ZHalf] (∀ i, F.obj i) => e (Pi.single i x) i) hgh
  simpa [nodesRep] using this

/-- `G_F(Z[1/2])` acting on the terminal algebra. -/
def terminalRep : F.autGroup →* (F.J ≃ₗ[ZHalf] F.J) := (jordanAut ZHalf F.J).subtype.comp (ev F)

theorem terminalRep_injective (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective F.terminalRep :=
  Subtype.val_injective.comp (ev_injective hν)

omit [TerminallyPointed I] in
/-- **Finite subgroups of a diagram group, through the action on all the nodes.** For a diagram
with finitely many objects and finite free nodes, with `M = ∏ᵢ F(i)` of rank `n`: every finite
subgroup preserves a finitely generated additive subgroup `L ⊆ M` with `Z[1/2] L = M`, has order at
most `3^(n²)` and lies in a maximal finite subgroup; and if the stabilizer of every such `L` is
finite, the maximal finite subgroups are the maximal members among these stabilizers. -/
theorem finite_subgroups_nodes [Finite I] [∀ i, Module.Finite ZHalf (F.obj i)]
    [∀ i, Module.Free ZHalf (F.obj i)] :
    (∀ H : Subgroup F.autGroup, Finite H →
      (∃ L : Submodule ℤ (∀ i, F.obj i), IsFGSpanning L ∧ H ≤ stabilizer F.nodesRep L) ∧
      Nat.card H ≤ 3 ^ (finrank ZHalf (∀ i, F.obj i) * finrank ZHalf (∀ i, F.obj i)) ∧
      ∃ K : Subgroup F.autGroup, H ≤ K ∧ Maximal (fun K : Subgroup F.autGroup => Finite K) K) ∧
    ((∀ L : Submodule ℤ (∀ i, F.obj i), IsFGSpanning L → Finite (stabilizer F.nodesRep L)) →
      ∀ K : Subgroup F.autGroup, Maximal (fun K : Subgroup F.autGroup => Finite K) K ↔
        Maximal (fun K => ∃ L, IsFGSpanning L ∧ K = stabilizer F.nodesRep L) K) :=
  ⟨fun H _ => ⟨exists_isFGSpanning_le_stabilizer F.nodesRep H,
      card_le F.nodesRep_injective H, exists_maximal_finite F.nodesRep_injective H⟩,
    fun hfin => maximal_finite_iff hfin⟩

/-- **Finite subgroups of a diagram group, through the action on the terminal algebra**, when the
terminal maps are injective: the same statements with `M` replaced by `F(+)`. -/
theorem finite_subgroups_terminal [Module.Finite ZHalf F.J] [Module.Free ZHalf F.J]
    (hν : ∀ i, Function.Injective (F.ν i)) :
    (∀ H : Subgroup F.autGroup, Finite H →
      (∃ L : Submodule ℤ F.J, IsFGSpanning L ∧ H ≤ stabilizer F.terminalRep L) ∧
      Nat.card H ≤ 3 ^ (finrank ZHalf F.J * finrank ZHalf F.J) ∧
      ∃ K : Subgroup F.autGroup, H ≤ K ∧ Maximal (fun K : Subgroup F.autGroup => Finite K) K) ∧
    ((∀ L : Submodule ℤ F.J, IsFGSpanning L → Finite (stabilizer F.terminalRep L)) →
      ∀ K : Subgroup F.autGroup, Maximal (fun K : Subgroup F.autGroup => Finite K) K ↔
        Maximal (fun K => ∃ L, IsFGSpanning L ∧ K = stabilizer F.terminalRep L) K) :=
  ⟨fun H _ => ⟨exists_isFGSpanning_le_stabilizer F.terminalRep H,
      card_le (F.terminalRep_injective hν) H, exists_maximal_finite (F.terminalRep_injective hν) H⟩,
    fun hfin => maximal_finite_iff hfin⟩

end JordanDiagram
