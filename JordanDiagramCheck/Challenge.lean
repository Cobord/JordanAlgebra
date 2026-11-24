module

public import JordanDiagram

/-!
# Challenge: trusted statements of the main results of `JordanDiagram`

This file is the **trusted specification** checked by `comparator` (see `README.md` in this
folder). Every theorem here is stated with `sorry`; `JordanDiagramCheck/Solution.lean` must prove
exactly the same statements, using only the axioms `propext`, `Quot.sound`, `Classical.choice`.

The statements use the definitions of the `JordanDiagram` library (diagrams, `autGroup`,
`derAlgebra`, `ev`, …), which are part of the trusted import closure. Where possible a result is
stated in elementary terms rather than through a library construction: the description of
spin-factor automorphisms, for instance, is "every automorphism of `J(V, B)` has the form
`(v, r) ↦ (g v, r)` for an isometry `g`", which does not depend on how `autEquivOrthogonal` is
built.

Review this file, not `Solution.lean`: if these statements say what is intended, a passing
`comparator` run certifies the formalization of them.
-/

@[expose] public section

-- The `sorry`s below are the intended placeholders of the challenge; silence their warnings.
set_option warn.sorry false

universe u u' v w w'

open CategoryTheory TerminallyPointed JordanAlgebra TensorProduct

namespace JordanDiagramCheck

section Diagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I] [TerminallyPointed I]

/-- **Terminal determination**. If the terminal maps are injective, terminal
evaluation `G_F(R) → Aut(J)` is injective with image the intersection of the stabilizers of the
images `Aᵢ = νᵢ(F(i))`. -/
theorem terminal_determination (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (JordanDiagram.ev F) ∧
      ∀ h : jordanAut R F.J, h ∈ (JordanDiagram.ev F).range ↔
        ∀ i, h '' F.image i = F.image i := by
  sorry

/-- **Terminal determination for derivations**. If the terminal maps are injective, terminal
evaluation on compatible derivations is injective with image `{D : D(Aᵢ) ⊆ Aᵢ for every i}`. -/
theorem compatible_derivations (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (JordanDiagram.evDer F) ∧
      Set.range (JordanDiagram.evDer F) =
        {d : JordanDerivation R F.J | ∀ i, ∀ y ∈ F.image i, d y ∈ F.image i} := by
  sorry

/-- **Wedges**. For a wedge `I⁺ = I₁⁺ ∪ I₂⁺`, restriction to the two halves is
injective with image the pairs agreeing at the terminal dot. -/
theorem wedge (F : JordanDiagram.{u, v} R I) {P₁ P₂ : ObjectProperty I}
    (hW : JordanDiagram.IsWedge P₁ P₂) :
    Function.Injective (JordanDiagram.wedgeHom (F := F) P₁ P₂) ∧
      Set.range (JordanDiagram.wedgeHom (F := F) P₁ P₂) =
        {p | p.1.1 ⟨top, hW.top₁⟩ = p.2.1 ⟨top, hW.top₂⟩} := by
  sorry

/-- **Terminal determination for isomorphisms**. If the terminal maps of
`F` and `F'` are injective, isomorphisms `F ≅ F'` correspond to Jordan isomorphisms `J ≃ J'`
carrying every `Aᵢ` onto `A'ᵢ`. -/
theorem iso_terminal_determination (F F' : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) (hν' : ∀ i, Function.Injective (F'.ν i)) :
    Nonempty (JordanDiagram.DiagramIso F F' ≃
      {h : F.J ≃ⱼ[R] F'.J // ∀ i, h '' F.image i = F'.image i}) := by
  sorry

/-- **Finite detector criterion** for generating configurations. A finite, `G_F(R)`-stable,
Jordan-generating subset `X` of the terminal algebra bounds `|G_F(R)|` by `|X|!`. -/
theorem finite_detector (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) {X : Set F.J} [Finite X]
    (hX : ∀ g : F.autGroup, ∀ x ∈ X, JordanDiagram.ev F g x ∈ X)
    (hgen : NonUnitalAlgebra.adjoin R X = ⊤) :
    Finite F.autGroup ∧ Nat.card F.autGroup ≤ (Nat.card X).factorial := by
  sorry

end Diagram

section ScalarExtension

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {A : Type v} [JordanAlgebra R A]
variable (S : Type u') [CommRing S] [Algebra R S]

/-- **Scalar extension**. With `2` invertible in `R`, the product on `S ⊗[R] A` is
commutative and satisfies the Jordan identity. Stated for Mathlib's product on the tensor
product, independently of the library's `JordanAlgebra` instance. -/
theorem scalar_extension (x y : S ⊗[R] A) :
    x * y = y * x ∧ x * x * (x * y) = x * (x * x * y) := by
  sorry

end ScalarExtension

section Functor

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} R I)
variable {S T U : Type u'} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  [CommRing U] [Algebra R U]

/-- **Functor laws for `G_F`**, and compatibility with `G_F(R) → G_F(S)`. -/
theorem autMap_functor (φ : S →ₐ[R] T) (χ : T →ₐ[R] U) :
    JordanDiagram.autMap F (AlgHom.id R S) = MonoidHom.id _ ∧
      JordanDiagram.autMap F (χ.comp φ) =
        (JordanDiagram.autMap F χ).comp (JordanDiagram.autMap F φ) ∧
      (JordanDiagram.autMap F φ).comp (JordanDiagram.autBaseChange S F) =
        JordanDiagram.autBaseChange T F := by
  sorry

/-- **Functor laws for `g_F`**, with brackets preserved. -/
theorem derMap_functor (φ : S →ₐ[R] T) (χ : T →ₐ[R] U) :
    JordanDiagram.derMap F (AlgHom.id R S) = LieRingHom.id ∧
      JordanDiagram.derMap F (χ.comp φ) =
        (JordanDiagram.derMap F χ).comp (JordanDiagram.derMap F φ) ∧
      ∀ D E, JordanDiagram.derMap F φ ⁅D, E⁆ =
        ⁅JordanDiagram.derMap F φ D, JordanDiagram.derMap F φ E⁆ := by
  sorry

/-- **Injectivity of the comparison map**. If every `F(i) → S ⊗ F(i)` is injective, so is
`G_F(R) → G_F(S)`. -/
theorem comparison_injective
    (h : ∀ i, Function.Injective (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)) :
    Function.Injective (JordanDiagram.autBaseChange S F) := by
  sorry

/-- **Image of the comparison map**. If every `a ↦ 1 ⊗ a` is injective, the image of
`G_F(R) → G_F(S)` is the set of automorphisms preserving every `1 ⊗ F(i)`. -/
theorem comparison_image
    (h : ∀ i, Function.Injective (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)) :
    Set.range (JordanDiagram.autBaseChange S F) =
      {g | ∀ i, g.1 i '' Set.range (fun a : F.obj i => (1 : S) ⊗ₜ[R] a) =
        Set.range (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)} := by
  sorry

end Functor

section SpinFactor

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type v} [AddCommGroup V]
  [Module R V] [Module.Free R V] (B : LinearMap.BilinForm R V) [Fact B.IsSymm]

open SpinFactor in
/-- **Spin-factor automorphisms**. For `V` free and `B` any symmetric bilinear form, every Jordan
automorphism of the spin factor `J(V, B) = V × R` is `(v, r) ↦ (g v, r)` for an isometry `g`. -/
theorem spinFactor_aut (a : jordanAut R (SpinFactor R V B)) :
    ∃ g : V ≃ₗ[R] V, (∀ v w, B (g v) (g w) = B v w) ∧ ∀ z : SpinFactor R V B,
      a z = SpinFactor.mk B (g z.1) z.2 := by
  sorry

open SpinFactor in
/-- **Spin-factor derivations**. Every derivation of `J(V, B)` is `(v, r) ↦ (X v, 0)` for a
`B`-skew `X`. -/
theorem spinFactor_der (d : JordanDerivation R (SpinFactor R V B)) :
    ∃ X : V →ₗ[R] V, (∀ v w, B (X v) w + B v (X w) = 0) ∧ ∀ z : SpinFactor R V B,
      d z = SpinFactor.mk B (X z.1) 0 := by
  sorry

end SpinFactor

open SpinFactor in
/-- **Orthogonal splitting** (one nonsingular member). For a symmetric form `B` nonsingular on
`W`, the stabilizer of `W` in `O(V, B)` is `O(W, B) × O(W⊥, B)`. No freeness or
`2`-invertibility needed. -/
theorem orthogonal_splitting {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm) (W : Submodule R V)
    (hW : IsNonsingularOn B W) :
    Nonempty (stabSub B W ≃*
      orthogonalGroup (B.restrict W) × orthogonalGroup (B.restrict (B.orthogonal W))) := by
  sorry

section SpinDiagram

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type u} [AddCommGroup V]
  [Module R V] (B : LinearMap.BilinForm R V) [Fact B.IsSymm]
  {I : Type w} [Preorder I] [OrderTop I] (W : I →o Submodule R V) [Module.Free R (W ⊤)]

open SpinFactor in
/-- **Spin-factor diagram automorphisms**. The automorphism group of the spin-factor diagram of
`(V, B, W)` is the stabilizer of the pieces `Wᵢ` in the orthogonal group of the terminal module. -/
theorem spin_diagram_group :
    Nonempty ((JordanDiagram.spinDiagram B W).autGroup ≃* JordanDiagram.orthStab B W) := by
  sorry

end SpinDiagram

end JordanDiagramCheck
