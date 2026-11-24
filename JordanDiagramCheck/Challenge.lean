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

/-- **Products of base rings**: `G_F` turns a product of base rings into a product of groups,
`(G_F(fst), G_F(snd)) : G_F(S × S') → G_F(S) × G_F(S')` being bijective. -/
theorem product_base_rings (S S' : Type u') [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] :
    Function.Bijective ((JordanDiagram.autMap F (AlgHom.fst R S S')).prod
      (JordanDiagram.autMap F (AlgHom.snd R S S'))) := by
  sorry

/-- **Specialization from power series**. Let every node of `F` be finite free and `S` be
torsion-free. For the constant-term map `S⟦X⟧ → S`, the kernel of `G_F(S⟦X⟧) → G_F(S)` is
torsion-free, so every finite subgroup of `G_F(S⟦X⟧)` embeds in `G_F(S)`; and the map is split
by the inclusion of constant series. -/
theorem power_series_specialization (S : Type u') [CommRing S] [Algebra R S]
    [IsAddTorsionFree S] [∀ i, Module.Free R (F.obj i)] [∀ i, Module.Finite R (F.obj i)] :
    (∀ g : (F.baseChange (PowerSeries S)).autGroup,
      JordanDiagram.autMap F (JordanDiagram.constCoeffAlg (R := R) S) g = 1 →
        ∀ k ≠ 0, g ^ k = 1 → g = 1) ∧
    (∀ H : Subgroup (F.baseChange (PowerSeries S)).autGroup, Finite H →
      Set.InjOn (JordanDiagram.autMap F (JordanDiagram.constCoeffAlg (R := R) S)) H) ∧
    (JordanDiagram.autMap F (JordanDiagram.constCoeffAlg (R := R) S)).comp
      (JordanDiagram.autMap F (JordanDiagram.constAlg S)) = MonoidHom.id _ := by
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

section Family

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]

/-- **`G_F` and `g_F` for families of diagrams over varying base rings**. For a family with
coherent base-change maps `β_φ`, `G_F(φ)(g)` is characterized by `G_F(φ)(g) ∘ β_φ = β_φ ∘ g` (and
likewise for `g_F`), and `G_F`, `g_F` satisfy the functor laws. -/
theorem family_functor (F : JordanDiagram.DiagramFamily.{u, u', v} R I)
    {S T U : CommAlgCat.{u'} R} (φ : S ⟶ T) (χ : T ⟶ U) :
    (∀ g i x, (F.autMap φ g).1 i (F.β φ i x) = F.β φ i (g.1 i x)) ∧
      (∀ D i x, (F.derMap φ D).1 i (F.β φ i x) = F.β φ i (D.1 i x)) ∧
      F.autMap (𝟙 S) = MonoidHom.id _ ∧ F.autMap (φ ≫ χ) = (F.autMap χ).comp (F.autMap φ) ∧
      F.derMap (𝟙 S) = LieRingHom.id ∧ F.derMap (φ ≫ χ) = (F.derMap χ).comp (F.derMap φ) := by
  sorry

/-- **The family of scalar extensions** `S ↦ S ⊗[R] F` of one diagram, with `β_φ = φ ⊗ 1`, has
the `G_F` and `g_F` of scalar extension. -/
theorem baseChangeFamily_functor [Invertible (2 : R)] (F : JordanDiagram.{u, v} R I)
    {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    (JordanDiagram.baseChangeFamily F).autMap φ = JordanDiagram.autMap F φ.hom ∧
      (JordanDiagram.baseChangeFamily F).derMap φ = JordanDiagram.derMap F φ.hom := by
  sorry

/-- **Every family is a scalar extension of its fiber over the base**: the coherence map along
`ι_S : R → S` identifies `F_S` with `S ⊗[R] F_R`, as diagrams, via `1 ⊗ a ↦ β_{ι_S}(a)`. -/
theorem family_base [Invertible (2 : R)] (F : JordanDiagram.DiagramFamily.{u, u, max u v} R I)
    (S : CommAlgCat.{u} R) :
    ∃ θ : JordanDiagram.DiagramIso ((F.base).baseChange S) (F.obj S),
      ∀ i a, θ.app i ((1 : S) ⊗ₜ[R] a) = F.β (JordanDiagram.unitHom R S) i a := by
  sorry

/-- **Ordered scalars and injective morphisms**: an injective morphism of ordered scalars carries
the positives of the source onto a coinitial subset of the positives of the target. -/
theorem ordered_coinitial [LinearOrder R] [Invertible (2 : R)]
    {A B : JordanDiagram.OrdScalar.{u, u'} R} (f : A ⟶ B) (hf : Function.Injective f.hom)
    (s : B) (hs : 0 < s) : ∃ r : A, 0 < r ∧ 0 < f.hom r ∧ f.hom r < s := by
  sorry

/-- **Power series as ordered scalars**. In the lowest-coefficient order on `A⟦t⟧`, `t` is a
positive infinitesimal. The constant-term map `A⟦t⟧ → A` is a morphism of ordered scalars, while
(for `2` invertible) there is no morphism `A → A⟦t⟧`: `A` is not initial. -/
theorem ordered_power_series {A : Type u} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]
    [Invertible (2 : A)] :
    (0 : PowerSeriesLC A) < JordanDiagram.PowerSeriesLC.t ∧
      (∀ a : A, 0 < a → JordanDiagram.PowerSeriesLC.t < algebraMap A (PowerSeriesLC A) a) ∧
      (∃ f : JordanDiagram.PowerSeriesLC.ordScalar A ⟶ JordanDiagram.PowerSeriesLC.baseObj A,
        ∀ x, f.hom x = PowerSeries.constantCoeff (PowerSeriesLC.toPowerSeries A x)) ∧
      IsEmpty (JordanDiagram.PowerSeriesLC.baseObj A ⟶ JordanDiagram.PowerSeriesLC.ordScalar A) := by
  sorry

/-- **Ordered scalars**. `G_F` and `g_F` restricted to the ordered scalar category act on a
continuous order-preserving morphism through its underlying algebra homomorphism. -/
theorem ordered_restriction [LinearOrder R] [Invertible (2 : R)] (F : JordanDiagram.{u, v} R I)
    {A B : JordanDiagram.OrdScalar.{u, u'} R} (f : A ⟶ B) :
    (JordanDiagram.orderedAutFunctor F).map f = GrpCat.ofHom (JordanDiagram.autMap F f.hom) ∧
      (JordanDiagram.orderedDerFunctor F).map f =
        LieRingCat.ofHom (JordanDiagram.derMap F f.hom) := by
  sorry

end Family

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

open SpinFactor in
/-- **Orthogonal flags**. Let `V = ⨁ⱼ Uⱼ` be an internal direct sum of mutually `B`-orthogonal
submodules, indexed by a finite linear order, with `B` nondegenerate on each piece. The stabilizer
in `O(V, B)` of the flag `W_j = ⨆_{i ≤ j} Uᵢ` is `∏ⱼ O(Uⱼ, B)`, by restriction to the pieces. -/
theorem orthogonal_flag {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) (hU : DirectSum.IsInternal U)
    (hO : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0)
    (hN : ∀ i, ∀ u ∈ U i, (∀ w ∈ U i, B u w = 0) → u = 0) :
    ∃ e : stabFamily B (fun j => ⨆ i : {i : ι // i ≤ j}, U i) ≃*
        ∀ j, orthogonalGroup (B.restrict (U j)),
      ∀ g j (u : U j), ((e g j : U j ≃ₗ[R] U j) u : V) =
        ((g : orthogonalGroup B) : V ≃ₗ[R] V) u := by
  sorry

/-- **Isomorphism of orthogonal flags**. Two orthogonal decompositions with nondegenerate pieces,
indexed by the same finite linear order, have isometric flags (an isometry `V ≃ V'` carrying
every `W_j = ⨆_{i ≤ j} Uᵢ` onto `W'_j`) exactly when the pieces `Uᵢ`, `U'ᵢ` are pairwise
isometric. -/
theorem orthogonal_flag_iso {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {V' : Type v} [AddCommGroup V'] [Module R V'] {ι : Type w} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (B : LinearMap.BilinForm R V) (B' : LinearMap.BilinForm R V')
    (U : ι → Submodule R V) (U' : ι → Submodule R V') (hU : DirectSum.IsInternal U)
    (hU' : DirectSum.IsInternal U')
    (hO : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0)
    (hO' : ∀ i j, i ≠ j → ∀ u ∈ U' i, ∀ w ∈ U' j, B' u w = 0)
    (hN : ∀ i, ∀ u ∈ U i, (∀ w ∈ U i, B u w = 0) → u = 0)
    (hN' : ∀ i, ∀ u ∈ U' i, (∀ w ∈ U' i, B' u w = 0) → u = 0) :
    (∃ g : V ≃ₗ[R] V', (∀ v w, B' (g v) (g w) = B v w) ∧
        ∀ j v, g v ∈ (⨆ i : {i : ι // i ≤ j}, U' i) ↔ v ∈ ⨆ i : {i : ι // i ≤ j}, U i) ↔
      ∀ i, ∃ g : U i ≃ₗ[R] U' i, ∀ x y, B' (g x) (g y) = B x y := by
  sorry

/-- **Orthogonal flags, Lie algebra**. For `V = ⨁ⱼ Uⱼ` with mutually orthogonal pieces on which
`B` is nondegenerate, restriction identifies the `B`-skew endomorphisms preserving the flag
`W_j = ⨆_{i ≤ j} Uᵢ` with the families of `B`-skew endomorphisms of the pieces. -/
theorem orthogonal_flag_lie {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) (hU : DirectSum.IsInternal U)
    (hO : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0)
    (hN : ∀ i, ∀ u ∈ U i, (∀ w ∈ U i, B u w = 0) → u = 0) :
    ∃ e : {X : V →ₗ[R] V // (∀ v w, B (X v) w + B v (X w) = 0) ∧
        ∀ j, ∀ v ∈ (⨆ i : {i : ι // i ≤ j}, U i), X v ∈ ⨆ i : {i : ι // i ≤ j}, U i} ≃
        ∀ j, {Y : U j →ₗ[R] U j // ∀ x y : U j, B (Y x) y + B x (Y y) = 0},
      ∀ X j (u : U j), ((e X j).1 u : V) = X.1 u := by
  sorry

/-- **The shape-twisted group**. For a diagram over a preorder, the twisted automorphisms
(a shape automorphism `σ` with compatible Jordan isomorphisms `F(i) ≃ F(σ i)`) form a group `G̃_F`,
and `1 → G_F → G̃_F → Aut(I)` is exact: viewing diagram automorphisms as twisted automorphisms
over the identity is injective, with image the kernel of the shape map. -/
theorem twisted_exact_sequence {R : Type u} [CommRing R] {I : Type w} [Preorder I]
    (F : JordanDiagram.{u, v} R I) :
    Function.Injective (JordanDiagram.TwistedAut.ofAut F) ∧
      (JordanDiagram.TwistedAut.ofAut F).range = (JordanDiagram.TwistedAut.shapeHom F).ker := by
  sorry

/-- **The wreath product**. For `U` free with a symmetric form, `2` invertible and `κ` finite,
let `F` be the spin-factor diagram over `κ` incomparable points below a top, with the `k`-th copy
of `U` at node `k` and `κ → U` (orthogonal sum form) at the top. Its shape-twisted group is
`O(U)^κ ⋊ Perm κ`, and the shape map is the permutation part. -/
theorem wreath_product {R : Type u} [CommRing R] [Invertible (2 : R)] {U : Type u}
    [AddCommGroup U] [Module R U] [Module.Free R U] (BU : LinearMap.BilinForm R U)
    [Fact BU.IsSymm] (κ : Type u) [Fintype κ] [DecidableEq κ] :
    ∃ e : JordanDiagram.TwistedAut (JordanDiagram.wreathDiagram BU κ) ≃*
        (κ → SpinFactor.orthogonalGroup BU) ⋊[JordanDiagram.permAct BU κ] Equiv.Perm κ,
      ∀ t, JordanDiagram.TwistedAut.shapeHom _ t = JordanDiagram.permShape (e t).right := by
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

/-- **The dyadic base ring**: a unital map `Z[1/2] → R` is unique, and exists exactly when `2` is a
unit in `R`. So `Z[1/2]`-algebras are the commutative rings in which `2` is invertible, and ring
maps between them automatically commute with the structure maps. -/
theorem zHalf_hom (R : Type u) [CommRing R] :
    Subsingleton (Localization.Away (2 : ℤ) →+* R) ∧
      (Nonempty (Localization.Away (2 : ℤ) →+* R) ↔ IsUnit (2 : R)) := by
  sorry

/-- **Norm coefficients of the generalized octonions**: the norm of the Cayley–Dickson algebra
with generators squaring to `a, b, c` (in Lean `Octonion R a b (-c)`) is diagonal in the standard
basis with coefficients `1, -a, -b, ab, -c, ac, bc, -abc`. -/
theorem octonion_norm_coefficients {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]
    {a b c : R} (x : Octonion R a b (-c)) :
    x * star x = Octonion.scalarEmbed (∑ i : Fin 8,
      ![1, -a, -b, a * b, -c, a * c, b * c, -(a * b * c)] i *
        ![x.1.re, x.1.imI, x.1.imJ, x.1.imK, x.2.re, x.2.imI, x.2.imJ, x.2.imK] i ^ 2) := by
  sorry

/-- **Positive norm coefficients**: over an ordered ring with `a, b, c < 0`, the eight norm
coefficients `1, -a, -b, ab, -c, ac, bc, -abc` are positive. -/
theorem octonion_norm_coefficients_pos {R : Type u} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : a < 0) (hb : b < 0) (hc : c < 0) (i : Fin 8) :
    0 < ![1, -a, -b, a * b, -c, a * c, b * c, -(a * b * c)] i := by
  sorry

/-- **The shape-twisted group for an arbitrary terminally pointed shape**: twisted automorphisms
`(u, θ)`, `u` a strict automorphism of `I⁺` fixing `+`, form a group, `1 → G_F → G̃_F → Aut(I⁺, +)`
is exact, and when the terminal maps are injective `(u, θ) ↦ (u, θ₊)` identifies `G̃_F` with the
pairs `(u, h)`, `h ∈ Aut(J)`, with `h(Aᵢ) = A_{u(i)}` for every `i`. -/
theorem shape_twisted_group {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]
    [TerminallyPointed I] (F : JordanDiagram.{u, v} R I) :
    Function.Injective (JordanDiagram.ShapeTwistedAut.ofAut F) ∧
      (JordanDiagram.ShapeTwistedAut.ofAut F).range =
        (JordanDiagram.ShapeTwistedAut.shapeHom F).ker ∧
      (∀ p, p ∈ JordanDiagram.ShapeTwistedAut.terminalPairs F ↔
        ∀ i, p.2 '' F.image i = F.image (p.1.functor.obj i)) ∧
      ((∀ i, Function.Injective (F.ν i)) →
        ∃ e : JordanDiagram.ShapeTwistedAut F ≃* JordanDiagram.ShapeTwistedAut.terminalPairs F,
          ∀ a, (e a : JordanDiagram.ShapeAut I × jordanAut R F.J) =
            (a.shape, JordanDiagram.ShapeTwistedAut.topAut a)) := by
  sorry

/-- **Minkowski's lemma, every level `m ≥ 3`**: an integer matrix `g ≡ 1 (mod m)` of finite order
is `1`; so every finite subgroup of `GL_N(ℤ)` embeds in `GL_N(ℤ/m)` under reduction. -/
theorem minkowski {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ} (hm : 3 ≤ m) :
    (∀ g : Matrix n n ℤ, (∀ a b, (m : ℤ) ∣ (g - 1) a b) → ∀ r ≠ 0, g ^ r = 1 → g = 1) ∧
      ∀ H : Subgroup (GL n ℤ), Finite H →
        Set.InjOn (Units.map ((Int.castRingHom (ZMod m)).mapMatrix (m := n)).toMonoidHom :
          GL n ℤ →* GL n (ZMod m)) (H : Set (GL n ℤ)) := by
  sorry

/-- **Formal reality of spin factors over a real closed field**: `J(V, B)` is formally real if
and only if `B` is positive definite. -/
theorem spinFactor_formallyReal_iff {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] {V : Type v} [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm) :
    @IsFormallyReal R (SpinFactor R V B) _ (SpinFactor.jordanAlgebra B hB) ↔
      B.toQuadraticMap.PosDef := by
  sorry

/-- **The ordered fraction field**: a totally ordered commutative ring is a domain, its fraction
field is totally ordered extending the order of `R`, and this is the only order making it a
totally ordered ring in which `R → K` is order-preserving. -/
theorem fraction_field_order (R : Type u) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    IsDomain R ∧ IsStrictOrderedRing (FractionRing R) ∧
      (∀ r s : R, algebraMap R (FractionRing R) r ≤ algebraMap R (FractionRing R) s ↔ r ≤ s) ∧
      ∀ o₁ o₂ : LinearOrder (FractionRing R),
        @IsStrictOrderedRing (FractionRing R) _ o₁.toPartialOrder →
        @IsStrictOrderedRing (FractionRing R) _ o₂.toPartialOrder →
        (∀ r s : R, r ≤ s → o₁.le (algebraMap R _ r) (algebraMap R _ s)) →
        (∀ r s : R, r ≤ s → o₂.le (algebraMap R _ r) (algebraMap R _ s)) →
        ∀ x y, o₁.le x y ↔ o₂.le x y := by
  sorry

/-- **An additive subgroup at the terminal node**: for an additive subgroup `L ⊆ J` and
`Lᵢ = νᵢ⁻¹(L)`, a diagram automorphism preserves `L` at the terminal node exactly when it preserves
every `Lᵢ`; if `L` spans `J` up to powers of `c`, each `Lᵢ` spans `F(i)` likewise; and if `L` is
finitely generated and `νᵢ` injective, `Lᵢ` is finitely generated. -/
theorem subgroup_at_terminal {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]
    [TerminallyPointed I] (F : JordanDiagram.{u, v} R I) (L : AddSubgroup F.J) :
    (∀ g : F.autGroup, g.1 top '' (L : Set F.J) = L ↔
      ∀ i, g.1 i '' (L.comap (F.ν i : F.obj i →+ F.J) : Set (F.obj i)) =
        L.comap (F.ν i : F.obj i →+ F.J)) ∧
      (∀ c : ℕ, (∀ y : F.J, ∃ k : ℕ, (c ^ k) • y ∈ L) →
        ∀ i (x : F.obj i), ∃ k : ℕ, (c ^ k) • x ∈ L.comap (F.ν i : F.obj i →+ F.J)) ∧
      (Module.Finite ℤ L → ∀ i, Function.Injective (F.ν i) →
        Module.Finite ℤ (L.comap (F.ν i : F.obj i →+ F.J))) := by
  sorry

/-- **Nonsingularity of the octonion norm**: the polar form of the norm of `O_R(a, b, c)` (in the
library's convention `Octonion R a b (-c)`) identifies the module with its dual exactly when
`a`, `b`, `c` are units. -/
theorem octonion_nonsingular {R : Type u} [CommRing R] [Invertible (2 : R)] [StarRing R]
    [TrivialStar R] (a b c : R) :
    Function.Bijective (Octonion.innerProduct : LinearMap.BilinForm R (Octonion R a b (-c))) ↔
      IsUnit a ∧ IsUnit b ∧ IsUnit c := by
  sorry

/-- **Finite subgroups preserve finitely generated spanning subgroups.** Let a group `G` act
faithfully on a finite free `Z[1/2]`-module `M` of rank `n`. Every finite subgroup preserves some
finitely generated additive subgroup `L ⊆ M` with `Z[1/2] L = M`, has order at most `3^(n²)`, and
lies in a maximal finite subgroup. If the stabilizer of every such `L` is finite, the maximal finite
subgroups are the maximal members among these stabilizers. -/
theorem finite_subgroups {M : Type u} [AddCommGroup M] [Module ZHalf M] [Module.Finite ZHalf M]
    [Module.Free ZHalf M] {G : Type v} [Group G] (ρ : G →* (M ≃ₗ[ZHalf] M))
    (hρ : Function.Injective ρ) :
    (∀ H : Subgroup G, Finite H →
      (∃ L : Submodule ℤ M, L.FG ∧ Submodule.span ZHalf (L : Set M) = ⊤ ∧
        ∀ g ∈ H, ∀ x, ρ g x ∈ L ↔ x ∈ L) ∧
      Nat.card H ≤ 3 ^ (Module.finrank ZHalf M * Module.finrank ZHalf M) ∧
      ∃ K : Subgroup G, H ≤ K ∧ Maximal (fun K : Subgroup G => Finite K) K) ∧
    ((∀ L : Submodule ℤ M, L.FG → Submodule.span ZHalf (L : Set M) = ⊤ →
        Finite (ZHalf.stabilizer ρ L)) →
      ∀ K : Subgroup G, Maximal (fun K : Subgroup G => Finite K) K ↔
        Maximal (fun K : Subgroup G => ∃ L : Submodule ℤ M, L.FG ∧
          Submodule.span ZHalf (L : Set M) = ⊤ ∧ K = ZHalf.stabilizer ρ L) K) := by
  sorry

/-- **The diagram group acts faithfully** on the product of the nodes, and on the terminal algebra
when the terminal maps are injective; so `finite_subgroups` applies to it. -/
theorem diagram_faithful {I : Type w} [Category.{w'} I] [TerminallyPointed I]
    (F : JordanDiagram.{0, v} ZHalf I) :
    Function.Injective F.nodesRep ∧
      ((∀ i, Function.Injective (F.ν i)) → Function.Injective F.terminalRep) := by
  sorry

/-- **Restriction along shapes is strictly functorial and commutes strictly with scalar
extension**, and for a fixed base ring its Grothendieck construction is a fibration over `Cat₊`. -/
theorem restriction_strict {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w}
    [Category.{w'} I] {I' I'' : Type w} [Category.{w'} I'] [Category.{w'} I''] (p : I'' ⥤ I')
    (p' : I' ⥤ I) (S : Type u) [CommRing S] [Algebra R S] :
    (JordanDiagram.restrictFunctor (𝟭 I) : JordanDiagram.{u, v} R I ⥤ _) = 𝟭 _ ∧
    (JordanDiagram.restrictFunctor (p ⋙ p') : JordanDiagram.{u, v} R I ⥤ _) =
      JordanDiagram.restrictFunctor p' ⋙ JordanDiagram.restrictFunctor p ∧
    (JordanDiagram.restrictFunctor p' ⋙ JordanDiagram.baseChangeFunctor I' S :
        JordanDiagram.{u, u} R I ⥤ _) =
      JordanDiagram.baseChangeFunctor I S ⋙ JordanDiagram.restrictFunctor p' ∧
    (Pseudofunctor.CoGrothendieck.forget
      (JordanDiagram.restrictionFunctor.{u, v, w, w'} R).toPseudofunctor').IsFibered := by
  sorry

/-- **Diagrams over varying shapes and base rings form a pseudofunctor**
`D : Cat₊ᵒᵖ × CAlg_{Z[1/2]} → Cat`, `(I, R) ↦ Fun(I, Jord_R)`, acting on a morphism `(u, f)` by
`diagramMap`: restriction along `u` followed by scalar extension along `f`. -/
theorem diagram_pseudofunctor :
    (∀ X : TPCat.{w, w'}ᵒᵖ × CommAlgCat.{u} ZHalf,
      (JordanDiagram.diagramPseudofunctor.obj ⟨X⟩ : Cat.{max u w, max (u + 1) w w'}) =
        Cat.of (JordanDiagram.{u, u} X.2 X.1.unop.carrier)) ∧
    ∀ {X Y : TPCat.{w, w'}ᵒᵖ × CommAlgCat.{u} ZHalf} (f : X ⟶ Y),
      (JordanDiagram.diagramPseudofunctor.map f.toLoc).toFunctor = JordanDiagram.diagramMap f := by
  sorry

end JordanDiagramCheck
