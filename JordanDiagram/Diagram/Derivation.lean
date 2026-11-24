import JordanDiagram.Diagram.Basic
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Compatible derivations of a diagram (Section 3.2)

`g_F(R) = Der(F_R)` (Definition 3.7): families `(Dᵢ)` of Jordan derivations with
`Dⱼ ∘ F(α) = F(α) ∘ Dᵢ` for every arrow `α`. Here it is `F.derAlgebra`, a Lie subalgebra of the
product Lie algebra `∀ i, JordanDerivation R (F.obj i)`.

* `evDer`: evaluation at the terminal dot, a Lie algebra homomorphism `g_F(R) → Der(J)`.
* `evDer_injective`, `range_evDer`: Proposition 3.8. When every terminal map `νᵢ` is injective,
  `evDer` is injective with image `{D : D(Aᵢ) ⊆ Aᵢ for every i}`.
* `restrictDer`: restriction along a functor `u : I' ⥤ I` (Lemma 3.11).

Mathlib has no Lie ring structure on a Pi type, so one is provided here (`Pi.instLieRing`,
`Pi.instLieAlgebra`), with the bracket taken componentwise.
-/

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

section PiLie

variable {ι : Type*} {L : ι → Type*}

/-- The componentwise Lie ring structure on a product of Lie rings. -/
instance Pi.instLieRing [∀ i, LieRing (L i)] : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie _ _ _ := funext fun _ => add_lie _ _ _
  lie_add _ _ _ := funext fun _ => lie_add _ _ _
  lie_self _ := funext fun _ => lie_self _
  leibniz_lie _ _ _ := funext fun _ => leibniz_lie _ _ _

theorem Pi.lie_apply [∀ i, LieRing (L i)] (x y : ∀ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ := rfl

/-- The componentwise Lie algebra structure on a product of Lie algebras. -/
instance Pi.instLieAlgebra (R : Type*) [CommRing R] [∀ i, LieRing (L i)]
    [∀ i, LieAlgebra R (L i)] : LieAlgebra R (∀ i, L i) where
  lie_smul _ _ _ := funext fun _ => lie_smul _ _ _

end PiLie

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} R I)

/-- The Lie algebra `g_F(R)` of compatible derivations (Definition 3.7). -/
def derAlgebra : LieSubalgebra R (∀ i, JordanDerivation R (F.obj i)) where
  carrier := {D | ∀ {i j : I} (α : i ⟶ j) (x : F.obj i), D j (F.map α x) = F.map α (D i x)}
  zero_mem' _ _ := by simp
  add_mem' {D E} hD hE i j α x := by
    simp only [Pi.add_apply, JordanDerivation.add_apply, hD α x, hE α x, map_add]
  smul_mem' r D hD i j α x := by
    simp only [Pi.smul_apply, JordanDerivation.smul_apply, hD α x, map_smul]
  lie_mem' {D E} hD hE i j α x := by
    simp only [Pi.lie_apply, JordanDerivation.lie_apply, hD α, hE α, map_sub]

variable {F}

theorem mem_derAlgebra {D : ∀ i, JordanDerivation R (F.obj i)} :
    D ∈ F.derAlgebra ↔ ∀ {i j : I} (α : i ⟶ j) (x : F.obj i), D j (F.map α x) = F.map α (D i x) :=
  Iff.rfl

section Restriction

variable {I' : Type*} [Category I']

/-- Restriction `g_F(R) → Der(F ∘ u)` along a functor `u : I' ⥤ I` (Lemma 3.11). -/
def restrictDer (u : I' ⥤ I) : F.derAlgebra →ₗ⁅R⁆ (F.restrict u).derAlgebra where
  toFun D := ⟨fun j => D.1 (u.obj j), fun α x => D.2 (u.map α) x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

end Restriction

section Terminal

variable [TerminallyPointed I]

variable (F) in
/-- Evaluation at the terminal dot, `g_F(R) → Der_R(J)`, `(Dᵢ) ↦ D₊` (Proposition 3.8). -/
def evDer : F.derAlgebra →ₗ⁅R⁆ JordanDerivation R F.J where
  toFun D := D.1 top
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp]
theorem evDer_apply (D : F.derAlgebra) : evDer F D = D.1 top := rfl

theorem evDer_ν (D : F.derAlgebra) (i : I) (x : F.obj i) :
    evDer F D (F.ν i x) = F.ν i (D.1 i x) :=
  D.2 (toTop i) x

/-- Injectivity of terminal evaluation on compatible derivations (Proposition 3.8). -/
theorem evDer_injective (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (evDer F) := by
  intro D E hDE
  apply Subtype.ext
  funext i
  ext x
  apply hν i
  rw [← evDer_ν, ← evDer_ν, hDE]

/-- The compatible family with terminal component `d`, for `d` preserving every image. -/
noncomputable def ofPreserving (hν : ∀ i, Function.Injective (F.ν i))
    (d : JordanDerivation R F.J) (hd : ∀ i, ∀ y ∈ F.image i, d y ∈ F.image i) : F.derAlgebra :=
  ⟨fun i => liftDer (hν i) d (fun x => hd i _ ⟨x, rfl⟩), by
    intro i j α x
    apply hν j
    rw [liftDer_spec, F.ν_map, F.ν_map, liftDer_spec]⟩

theorem evDer_ofPreserving (hν : ∀ i, Function.Injective (F.ν i))
    (d : JordanDerivation R F.J) (hd : ∀ i, ∀ y ∈ F.image i, d y ∈ F.image i) :
    evDer F (ofPreserving hν d hd) = d := by
  ext x
  have := liftDer_spec (hν top) d (fun x => hd top _ ⟨x, rfl⟩) x
  rwa [F.ν_top, F.ν_top] at this

/-- **Proposition 3.8**: when the terminal maps are injective, the image of terminal evaluation on
compatible derivations is `{D ∈ Der_R(J) : D(Aᵢ) ⊆ Aᵢ for every i}`. -/
theorem range_evDer (hν : ∀ i, Function.Injective (F.ν i)) :
    Set.range (evDer F) = {d | ∀ i, ∀ y ∈ F.image i, d y ∈ F.image i} := by
  ext d
  constructor
  · rintro ⟨D, rfl⟩ i _ ⟨x, rfl⟩
    exact ⟨D.1 i x, (evDer_ν D i x).symm⟩
  · intro hd
    exact ⟨ofPreserving hν d hd, evDer_ofPreserving hν d hd⟩

end Terminal

end JordanDiagram
