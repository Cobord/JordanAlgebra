module

public import JordanDiagram.Diagram.SpinFactor
public import JordanDiagram.Algebra.DyadicFinite
public import JordanDiagram.Algebra.OrthogonalFlag
public import JordanDiagram.Algebra.ChainFinite

/-!
# Dyadic points of definite spin-factor diagrams

For a spin-factor diagram over `Z[1/2]` on `(V, B, W)` whose top piece `W ⊤` is free with a form
positive over `ℝ` and anisotropic over `ℚ₂`, the diagram group `G_F(Z[1/2])` is finite
(`finite_spinDiagram`): it is the stabilizer of the pieces in `O(W ⊤, B)(Z[1/2])`, which is finite
by `ZHalf.finite_of_form`. For an orthogonal flag `W_j = ⨆_{i ≤ j} Uᵢ`, whose stabilizer is
`∏ⱼ O(Uⱼ, B)`, it suffices that every piece is anisotropic over `ℚ₂` (`finite_stabFlag`), although
their sum need not be.
-/

@[expose] public section

open SpinFactor ZHalf Matrix Module

namespace JordanDiagram

theorem ZHalf.isUnit_two : IsUnit (2 : ZHalf) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (2 : ℤ) (S := ZHalf)

section OrthRep

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
  (B : LinearMap.BilinForm R V) (U : Submodule R V)

/-- `O(U, B|_U)` acting on a submodule `U`. Stated over a general ring, where the two additive
structures of `U` (as a submodule, and through its additive group) are unified by unfolding; over
`Z[1/2]` the unfolding is not available. -/
def orthRep : orthogonalGroup (B.restrict U) →*
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ U U U.addCommMonoid U.addCommMonoid
      U.module U.module :=
  (orthogonalGroup (B.restrict U)).subtype

theorem orthRep_injective : Function.Injective (orthRep B U) := Subtype.val_injective

theorem orthRep_isometry (g : orthogonalGroup (B.restrict U)) (x y : U) :
    B.restrict U (orthRep B U g x) (orthRep B U g y) = B.restrict U x y :=
  g.2 x y

end OrthRep

section TopChain

universe u

variable {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V] {I : Type*}
  [Preorder I] [OrderTop I] (W : I →o Submodule R V)

/-- The members `Wᵢ` as submodules of the terminal module `W ⊤`. As for `orthRep`, this is stated
over a general ring so that the additive structure of `W ⊤` matches the one `chainPiece` uses. -/
def topChain (i : I) : @Submodule R (W ⊤) _ AddCommGroup.toAddCommMonoid (W ⊤).module :=
  (W i).comap (W ⊤).subtype

theorem mem_topChain {i : I} {u : W ⊤} : u ∈ topChain W i ↔ (u : V) ∈ W i := Iff.rfl

theorem topChain_mono : Monotone (topChain W) := fun _ _ h _ hu => W.monotone h hu

theorem topChain_top : topChain W ⊤ = ⊤ := Submodule.comap_subtype_self _

/-- `Wᵢ` seen inside `W ⊤` is isomorphic to `Wᵢ`. -/
def topChainEquiv (i : I) : topChain W i ≃ₗ[R] W i :=
  Submodule.comapSubtypeEquivOfLe (W.monotone le_top)

variable (B : LinearMap.BilinForm R V)

/-- The stabilizer of a spin-factor diagram preserves every member, seen inside `W ⊤`. -/
theorem orthStab_topChain : ∀ g ∈ orthStab B W, ∀ i (v : W ⊤),
    (g : W ⊤ ≃ₗ[R] W ⊤) v ∈ topChain W i ↔ v ∈ topChain W i :=
  fun _ hg i v => hg i v

variable {n : ℕ} (W : Fin (n + 1) →o Submodule R V)

/-- The pieces `W₀` and `W_{j+1} ∩ W_j^⊥` of a chain, inside `W ⊤`. -/
def spinChainPiece (j : Fin (n + 1)) : Submodule R (W ⊤) :=
  chainPiece (B.restrict (W ⊤)) (topChain W) j

/-- **Reduction to the pieces** for spin-factor diagrams on a chain: over a domain, for finite free
members and an anisotropic form, `G_F(R)` is finite when its image on every piece is. -/
theorem finite_spinDiagram_of_pieces [IsDomain R] [Invertible (2 : R)] [Module.Free R (W ⊤)]
    [Fact B.IsSymm] (hB : ∀ v, B v v = 0 → v = 0) {κ : Fin (n + 1) → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)] (b : ∀ j, Basis (κ j) R (W j))
    (hfin : ∀ j, Finite (chainPieceRep (B.restrict (W ⊤)) (orthStab_topChain W B) j).range) :
    Finite (spinDiagram B W).autGroup := by
  have := finite_of_finite_chainPieceRep (B.restrict (W ⊤)) (orthStab_topChain W B)
    (topChain_mono W) (topChain_top W) (fun v hv => Subtype.ext (hB v hv))
    (fun j => (b j).map (topChainEquiv W j).symm) hfin
  exact Finite.of_equiv _ (spinDiagramAutEquiv B W).symm.toEquiv

end TopChain

variable {V : Type} [AddCommGroup V] [Module ZHalf V] (B : LinearMap.BilinForm ZHalf V)
  [Fact B.IsSymm] {I : Type*} [Preorder I] [OrderTop I]

/-- **Definite spin-factor diagrams have finitely many dyadic points** when the form on the top
piece is anisotropic over `ℚ₂`. -/
theorem finite_spinDiagram (W : I →o Submodule ZHalf V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ZHalf (W ⊤)) (hpos : ∀ v, v ≠ 0 → 0 < toRat (B v v))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun i j => ((toRat (B (b i) (b j)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (spinDiagram B W).autGroup := by
  let : Invertible (2 : ZHalf) := ZHalf.isUnit_two.invertible
  have : Module.Free ZHalf (W ⊤) := Module.Free.of_basis b
  -- the type is left to be inferred from `orthRep`: written out over `Z[1/2]` directly, its
  -- instances would take a path that cannot be unfolded to this one
  have := finite_of_form (M := W ⊤) b (ρ := orthRep B (W ⊤)) (orthRep_injective B (W ⊤))
    (B.restrict (W ⊤)) (orthRep_isometry B (W ⊤))
    (fun x hx => hpos x fun h => hx (Submodule.coe_eq_zero.1 h)) h2
  exact Finite.of_equiv _ (spinDiagramAutEquiv B W).symm.toEquiv

omit [Fact B.IsSymm] in
/-- **Orthogonal flags with anisotropic pieces have finitely many dyadic points**: for
`V = ⨁ⱼ Uⱼ` with mutually orthogonal nondegenerate pieces, each free with a form positive over `ℝ`
and anisotropic over `ℚ₂` (no condition on a zero piece, whose basis is empty), the stabilizer in
`O(V, B)(Z[1/2])` of the flag `W_j = ⨆_{i ≤ j} Uᵢ` is finite. -/
theorem finite_stabFlag {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {U : ι → Submodule ZHalf V} (hU : DirectSum.IsInternal U) (hO : PairwiseOrthogonal B U)
    (hN : ∀ i, NondegenerateOn B (U i)) {κ : ι → Type*} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)] (b : ∀ j, Basis (κ j) ZHalf (U j))
    (hpos : ∀ v, v ≠ 0 → 0 < toRat (B v v))
    (h2 : ∀ j (v : κ j → ℚ_[2]), v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun k k' => ((toRat (B (b j k) (b j k')) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (stabFlag B U) := by
  have := fun j => finite_of_form (M := U j) (b j) (ρ := orthRep B (U j))
    (orthRep_injective B (U j)) (B.restrict (U j)) (orthRep_isometry B (U j))
    (fun x hx => hpos x fun h => hx (Submodule.coe_eq_zero.1 h)) (h2 j)
  exact Finite.of_equiv _ (stabFlagEquivPi hU hO hN).symm.toEquiv

/-- **Chains of free submodules with anisotropic pieces have finitely many dyadic points**: for a
spin-factor diagram on a chain `W₀ ⊆ ⋯ ⊆ Wₙ` of finite free `Z[1/2]`-modules with a positive form,
whose members need not be direct summands, `G_F(Z[1/2])` is finite when every piece `W₀`,
`W_{j+1} ∩ W_j^⊥` has a basis in which the form is anisotropic over `ℚ₂`. -/
theorem finite_spinDiagram_chain {n : ℕ} (W : Fin (n + 1) →o Submodule ZHalf V)
    {κ : Fin (n + 1) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (b : ∀ j, Basis (κ j) ZHalf (W j))
    {κ' : Fin (n + 1) → Type*} [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (bp : ∀ j, Basis (κ' j) ZHalf (spinChainPiece B W j))
    (hpos : ∀ v, v ≠ 0 → 0 < toRat (B v v))
    (h2 : ∀ j (v : κ' j → ℚ_[2]), v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun k k' =>
        ((toRat (B ((bp j k : W ⊤) : V) ((bp j k' : W ⊤) : V)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (spinDiagram B W).autGroup := by
  let : Invertible (2 : ZHalf) := ZHalf.isUnit_two.invertible
  have : Module.Free ZHalf (W ⊤) := Module.Free.of_basis (b ⊤)
  have hB : ∀ v, B v v = 0 → v = 0 := fun v h => by
    by_contra hv
    have := hpos v hv
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  exact finite_spinDiagram_of_pieces B W hB b fun j =>
    ZHalf.finite_range_chainPieceRep _ _ (bp j)
      (fun x hx => hpos _ fun h => hx (Subtype.ext (Subtype.ext h))) (h2 j)

end JordanDiagram
