module

public import JordanDiagram.Algebra.Automorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Terminally pointed Jordan diagrams (Section 2.2)

A *terminally pointed indexing category* `(I⁺, +)` (Definition 2.5) is a small category with a
specified terminal object; `TerminallyPointed I` records the choice. A Jordan diagram over a fixed
commutative ring `R` is a functor `I⁺ → Jord_R`, where `Jord_R` has Jordan algebras as objects and
non-unital algebra homomorphisms (`R`-linear maps preserving the product, units ignored) as
morphisms. Rather than bundling `Jord_R` as a Mathlib category, `JordanDiagram R I` records the
functor concretely: a family of Jordan algebras `obj i` with maps `map α` satisfying functoriality.

The terminal algebra is `J = obj ⊤` and the terminal maps are `ν i = map (! i) : obj i → J`
(Definition 2.8). The scalar-extension coherence (the family over varying `R`) is not part of this
file: everything here is fiberwise, over one ring.
-/

@[expose] public section

universe u v w w'

open CategoryTheory

/-- A terminally pointed indexing category: a category with a specified terminal object. -/
class TerminallyPointed (I : Type w) [Category.{w'} I] where
  /-- The terminal dot `+`. -/
  top : I
  /-- The terminal dot is terminal. -/
  isTerminal : Limits.IsTerminal top

namespace TerminallyPointed

variable {I : Type w} [Category.{w'} I] [TerminallyPointed I]

/-- The unique arrow `!ᵢ : i ⟶ +`. -/
def toTop (i : I) : i ⟶ top := isTerminal.from i

theorem hom_ext {i : I} (f g : i ⟶ top) : f = g := isTerminal.hom_ext f g

theorem toTop_top : toTop (top : I) = 𝟙 top := hom_ext _ _

theorem comp_toTop {i j : I} (α : i ⟶ j) : α ≫ toTop j = toTop i := hom_ext _ _

end TerminallyPointed

/-- A preorder with a greatest element, as a category, is terminally pointed by `⊤`; e.g. a poset
`P` with a greatest element adjoined, `WithTop P` (Definition 5.3). -/
instance TerminallyPointed.ofOrderTop (I : Type w) [Preorder I] [OrderTop I] :
    TerminallyPointed I :=
  ⟨⊤, Preorder.isTerminalTop I⟩

/-- A diagram `I → Jord_R` of Jordan algebras over a fixed commutative ring `R`. Arrows are
non-unital algebra homomorphisms: a unit need not exist, and need not be preserved when it does
(e.g. corner inclusions, Lemma 8.14). -/
structure JordanDiagram (R : Type u) [CommRing R] (I : Type w) [Category.{w'} I] where
  /-- The Jordan algebra at node `i`. -/
  obj : I → Type v
  [jordan : ∀ i, JordanAlgebra R (obj i)]
  /-- The Jordan homomorphism attached to an arrow. -/
  map : ∀ {i j : I}, (i ⟶ j) → (obj i →ₙₐ[R] obj j)
  map_id : ∀ (i : I) (x : obj i), map (𝟙 i) x = x
  map_comp : ∀ {i j k : I} (α : i ⟶ j) (β : j ⟶ k) (x : obj i),
    map (α ≫ β) x = map β (map α x)

attribute [instance] JordanDiagram.jordan

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]

section Restriction

variable {I' : Type*} [Category I']

/-- Restriction of a diagram along a functor `u : I' ⥤ I` (Lemma 3.11). Reducible, so that its
nodes are seen as `F.obj (u.obj j)` by rewriting and instance search. -/
@[reducible] def restrict (F : JordanDiagram.{u, v} R I) (u : I' ⥤ I) : JordanDiagram.{u, v} R I' where
  obj j := F.obj (u.obj j)
  map α := F.map (u.map α)
  map_id j x := by rw [u.map_id]; exact F.map_id _ x
  map_comp α β x := by rw [u.map_comp]; exact F.map_comp _ _ x

end Restriction

section Terminal

variable [TerminallyPointed I] (F : JordanDiagram.{u, v} R I)

open TerminallyPointed

/-- The terminal Jordan algebra `J = F(+)`. -/
abbrev J : Type v := F.obj top

/-- The terminal map `νᵢ = F(!ᵢ) : F(i) → J`. -/
def ν (i : I) : F.obj i →ₙₐ[R] F.J := F.map (toTop i)

theorem ν_top (x : F.J) : F.ν top x = x := by
  rw [ν, toTop_top, F.map_id]

/-- The terminal relation `ν_j ∘ F(α) = ν_i`. -/
theorem ν_map {i j : I} (α : i ⟶ j) (x : F.obj i) : F.ν j (F.map α x) = F.ν i x := by
  rw [ν, ν, ← F.map_comp, comp_toTop]

/-- The image `Aᵢ = νᵢ(F(i)) ⊆ J`. -/
abbrev image (i : I) : Set F.J := Set.range (F.ν i)

end Terminal

end JordanDiagram
