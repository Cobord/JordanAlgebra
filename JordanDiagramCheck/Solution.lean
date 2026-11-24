module

public import JordanDiagram

/-!
# Solution: proofs of the statements in `Challenge.lean`

Each theorem restates the corresponding one in `JordanDiagramCheck/Challenge.lean` verbatim and
proves it from the `JordanDiagram` library. `comparator` checks that the statements agree and that
only `propext`, `Quot.sound`, `Classical.choice` are used.
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory TerminallyPointed JordanAlgebra TensorProduct

namespace JordanDiagramCheck

section Diagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I] [TerminallyPointed I]

theorem terminal_determination (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (JordanDiagram.ev F) ∧
      ∀ h : jordanAut R F.J, h ∈ (JordanDiagram.ev F).range ↔
        ∀ i, h '' F.image i = F.image i := by
  refine ⟨JordanDiagram.ev_injective hν, fun h => ?_⟩
  rw [JordanDiagram.range_ev hν, JordanDiagram.mem_stabImages]

theorem compatible_derivations (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (JordanDiagram.evDer F) ∧
      Set.range (JordanDiagram.evDer F) =
        {d : JordanDerivation R F.J | ∀ i, ∀ y ∈ F.image i, d y ∈ F.image i} :=
  ⟨JordanDiagram.evDer_injective hν, JordanDiagram.range_evDer hν⟩

theorem wedge (F : JordanDiagram.{u, v} R I) {P₁ P₂ : ObjectProperty I}
    (hW : JordanDiagram.IsWedge P₁ P₂) :
    Function.Injective (JordanDiagram.wedgeHom (F := F) P₁ P₂) ∧
      Set.range (JordanDiagram.wedgeHom (F := F) P₁ P₂) =
        {p | p.1.1 ⟨top, hW.top₁⟩ = p.2.1 ⟨top, hW.top₂⟩} :=
  ⟨JordanDiagram.wedgeHom_injective hW, JordanDiagram.range_wedgeHom hW⟩

theorem iso_terminal_determination (F F' : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) (hν' : ∀ i, Function.Injective (F'.ν i)) :
    Nonempty (JordanDiagram.DiagramIso F F' ≃
      {h : F.J ≃ⱼ[R] F'.J // ∀ i, h '' F.image i = F'.image i}) :=
  ⟨JordanDiagram.DiagramIso.terminalEquiv hν hν'⟩

theorem finite_detector (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) {X : Set F.J} [Finite X]
    (hX : ∀ g : F.autGroup, ∀ x ∈ X, JordanDiagram.ev F g x ∈ X)
    (hgen : NonUnitalAlgebra.adjoin R X = ⊤) :
    Finite F.autGroup ∧ Nat.card F.autGroup ≤ (Nat.card X).factorial :=
  JordanDiagram.card_autGroup_le hν hX hgen

end Diagram

section ScalarExtension

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {A : Type v} [JordanAlgebra R A]
variable (S : Type u') [CommRing S] [Algebra R S]

theorem scalar_extension (x y : S ⊗[R] A) :
    x * y = y * x ∧ x * x * (x * y) = x * (x * x * y) :=
  ⟨BaseChange.mul_comm' S x y, JordanAlgebra.jordan_identity x y⟩

end ScalarExtension

section Functor

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} R I)
variable {S T U : Type u'} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  [CommRing U] [Algebra R U]

theorem autMap_functor (φ : S →ₐ[R] T) (χ : T →ₐ[R] U) :
    JordanDiagram.autMap F (AlgHom.id R S) = MonoidHom.id _ ∧
      JordanDiagram.autMap F (χ.comp φ) =
        (JordanDiagram.autMap F χ).comp (JordanDiagram.autMap F φ) ∧
      (JordanDiagram.autMap F φ).comp (JordanDiagram.autBaseChange S F) =
        JordanDiagram.autBaseChange T F :=
  ⟨JordanDiagram.autMap_id F, JordanDiagram.autMap_comp F φ χ,
    JordanDiagram.autMap_comp_autBaseChange F φ⟩

theorem product_base_rings (S S' : Type u') [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] :
    Function.Bijective ((JordanDiagram.autMap F (AlgHom.fst R S S')).prod
      (JordanDiagram.autMap F (AlgHom.snd R S S'))) :=
  JordanDiagram.autMap_prod_bijective F S S'

theorem power_series_specialization (S : Type u') [CommRing S] [Algebra R S]
    [IsAddTorsionFree S] [∀ i, Module.Free R (F.obj i)] [∀ i, Module.Finite R (F.obj i)] :
    (∀ g : (F.baseChange (PowerSeries S)).autGroup,
      JordanDiagram.autMap F (JordanDiagram.constCoeffAlg (R := R) S) g = 1 →
        ∀ k ≠ 0, g ^ k = 1 → g = 1) ∧
    (∀ H : Subgroup (F.baseChange (PowerSeries S)).autGroup, Finite H →
      Set.InjOn (JordanDiagram.autMap F (JordanDiagram.constCoeffAlg (R := R) S)) H) ∧
    (JordanDiagram.autMap F (JordanDiagram.constCoeffAlg (R := R) S)).comp
      (JordanDiagram.autMap F (JordanDiagram.constAlg S)) = MonoidHom.id _ :=
  ⟨fun g h0 _ hk hg => JordanDiagram.autMap_const_eq_one S F g h0 hk hg,
    fun H _ => JordanDiagram.injOn_autMap_const S F H,
    JordanDiagram.autMap_const_comp_autMap_C S F⟩

theorem derMap_functor (φ : S →ₐ[R] T) (χ : T →ₐ[R] U) :
    JordanDiagram.derMap F (AlgHom.id R S) = LieRingHom.id ∧
      JordanDiagram.derMap F (χ.comp φ) =
        (JordanDiagram.derMap F χ).comp (JordanDiagram.derMap F φ) ∧
      ∀ D E, JordanDiagram.derMap F φ ⁅D, E⁆ =
        ⁅JordanDiagram.derMap F φ D, JordanDiagram.derMap F φ E⁆ :=
  ⟨JordanDiagram.derMap_id F, JordanDiagram.derMap_comp F φ χ,
    (JordanDiagram.derMap F φ).map_lie⟩

theorem comparison_injective
    (h : ∀ i, Function.Injective (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)) :
    Function.Injective (JordanDiagram.autBaseChange S F) :=
  JordanDiagram.autBaseChange_injective h

theorem comparison_image
    (h : ∀ i, Function.Injective (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)) :
    Set.range (JordanDiagram.autBaseChange S F) =
      {g | ∀ i, g.1 i '' Set.range (fun a : F.obj i => (1 : S) ⊗ₜ[R] a) =
        Set.range (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)} :=
  JordanDiagram.range_autBaseChange h

end Functor

section Family

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]

theorem family_functor (F : JordanDiagram.DiagramFamily.{u, u', v} R I)
    {S T U : CommAlgCat.{u'} R} (φ : S ⟶ T) (χ : T ⟶ U) :
    (∀ g i x, (F.autMap φ g).1 i (F.β φ i x) = F.β φ i (g.1 i x)) ∧
      (∀ D i x, (F.derMap φ D).1 i (F.β φ i x) = F.β φ i (D.1 i x)) ∧
      F.autMap (𝟙 S) = MonoidHom.id _ ∧ F.autMap (φ ≫ χ) = (F.autMap χ).comp (F.autMap φ) ∧
      F.derMap (𝟙 S) = LieRingHom.id ∧ F.derMap (φ ≫ χ) = (F.derMap χ).comp (F.derMap φ) :=
  ⟨F.autMap_β φ, F.derMap_β φ, F.autMap_id S, F.autMap_comp φ χ, F.derMap_id S,
    F.derMap_comp φ χ⟩

theorem baseChangeFamily_functor [Invertible (2 : R)] (F : JordanDiagram.{u, v} R I)
    {S T : CommAlgCat.{u'} R} (φ : S ⟶ T) :
    (JordanDiagram.baseChangeFamily F).autMap φ = JordanDiagram.autMap F φ.hom ∧
      (JordanDiagram.baseChangeFamily F).derMap φ = JordanDiagram.derMap F φ.hom :=
  ⟨JordanDiagram.baseChangeFamily_autMap F φ, JordanDiagram.baseChangeFamily_derMap F φ⟩

theorem family_base [Invertible (2 : R)] (F : JordanDiagram.DiagramFamily.{u, u, max u v} R I)
    (S : CommAlgCat.{u} R) :
    ∃ θ : JordanDiagram.DiagramIso ((F.base).baseChange S) (F.obj S),
      ∀ i a, θ.app i ((1 : S) ⊗ₜ[R] a) = F.β (JordanDiagram.unitHom R S) i a :=
  ⟨F.baseIso S, F.baseIso_one_tmul S⟩

theorem ordered_coinitial [LinearOrder R] [Invertible (2 : R)]
    {A B : JordanDiagram.OrdScalar.{u, u'} R} (f : A ⟶ B) (hf : Function.Injective f.hom)
    (s : B) (hs : 0 < s) : ∃ r : A, 0 < r ∧ 0 < f.hom r ∧ f.hom r < s :=
  JordanDiagram.OrdScalar.exists_pos_lt_of_injective f hf hs

theorem ordered_power_series {A : Type u} [CommRing A] [LinearOrder A] [IsStrictOrderedRing A]
    [Invertible (2 : A)] :
    (0 : PowerSeriesLC A) < JordanDiagram.PowerSeriesLC.t ∧
      (∀ a : A, 0 < a → JordanDiagram.PowerSeriesLC.t < algebraMap A (PowerSeriesLC A) a) ∧
      (∃ f : JordanDiagram.PowerSeriesLC.ordScalar A ⟶ JordanDiagram.PowerSeriesLC.baseObj A,
        ∀ x, f.hom x = PowerSeries.constantCoeff (PowerSeriesLC.toPowerSeries A x)) ∧
      IsEmpty (JordanDiagram.PowerSeriesLC.baseObj A ⟶ JordanDiagram.PowerSeriesLC.ordScalar A) :=
  ⟨JordanDiagram.PowerSeriesLC.t_pos, fun _ ha => JordanDiagram.PowerSeriesLC.t_lt_C ha,
    ⟨JordanDiagram.PowerSeriesLC.constTermHom, fun _ => rfl⟩,
    JordanDiagram.PowerSeriesLC.isEmpty_hom⟩

theorem ordered_restriction [LinearOrder R] [Invertible (2 : R)] (F : JordanDiagram.{u, v} R I)
    {A B : JordanDiagram.OrdScalar.{u, u'} R} (f : A ⟶ B) :
    (JordanDiagram.orderedAutFunctor F).map f = GrpCat.ofHom (JordanDiagram.autMap F f.hom) ∧
      (JordanDiagram.orderedDerFunctor F).map f =
        LieRingCat.ofHom (JordanDiagram.derMap F f.hom) :=
  ⟨JordanDiagram.orderedAutFunctor_map F f, JordanDiagram.orderedDerFunctor_map F f⟩

end Family

section SpinFactor

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type v} [AddCommGroup V]
  [Module R V] [Module.Free R V] (B : LinearMap.BilinForm R V) [Fact B.IsSymm]

open SpinFactor in
theorem spinFactor_aut (a : jordanAut R (SpinFactor R V B)) :
    ∃ g : V ≃ₗ[R] V, (∀ v w, B (g v) (g w) = B v w) ∧ ∀ z : SpinFactor R V B,
      a z = SpinFactor.mk B (g z.1) z.2 :=
  ⟨(orthogonalOfAut a).1, (orthogonalOfAut a).2, fun z =>
    (congrArg (fun b : jordanAut R (SpinFactor R V B) => b z)
      (autOfOrthogonal_orthogonalOfAut a)).symm⟩

open SpinFactor in
theorem spinFactor_der (d : JordanDerivation R (SpinFactor R V B)) :
    ∃ X : V →ₗ[R] V, (∀ v w, B (X v) w + B v (X w) = 0) ∧ ∀ z : SpinFactor R V B,
      d z = SpinFactor.mk B (X z.1) 0 :=
  ⟨derVecPart d, derVecPart_isSkew d, fun z =>
    (JordanDerivation.congr_fun (derOfSkew_derVecPart d) z).symm⟩

end SpinFactor

open SpinFactor in
theorem orthogonal_splitting {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm) (W : Submodule R V)
    (hW : IsNonsingularOn B W) :
    Nonempty (stabSub B W ≃*
      orthogonalGroup (B.restrict W) × orthogonalGroup (B.restrict (B.orthogonal W))) :=
  ⟨stabEquivProd hB hW⟩

open SpinFactor in
theorem orthogonal_flag {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) (hU : DirectSum.IsInternal U)
    (hO : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0)
    (hN : ∀ i, ∀ u ∈ U i, (∀ w ∈ U i, B u w = 0) → u = 0) :
    ∃ e : stabFamily B (fun j => ⨆ i : {i : ι // i ≤ j}, U i) ≃*
        ∀ j, orthogonalGroup (B.restrict (U j)),
      ∀ g j (u : U j), ((e g j : U j ≃ₗ[R] U j) u : V) =
        ((g : orthogonalGroup B) : V ≃ₗ[R] V) u :=
  ⟨stabFlagEquivPi hU hO hN, stabFlagEquivPi_apply hU hO hN⟩

open SpinFactor in
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
  have key := nonempty_flagIsometry_iff hU hU' hO hO' hN hN'
  constructor
  · rintro ⟨g, hg, hfl⟩ i
    obtain ⟨e⟩ := key.1 ⟨⟨⟨g, hg⟩, hfl⟩⟩ i
    exact ⟨e.1, e.2⟩
  · intro h
    obtain ⟨⟨⟨g, hg⟩, hfl⟩⟩ := key.2 fun i => (h i).elim fun e he => ⟨⟨e, he⟩⟩
    exact ⟨g, hg, hfl⟩

open SpinFactor in
theorem orthogonal_flag_lie {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : LinearMap.BilinForm R V) (U : ι → Submodule R V) (hU : DirectSum.IsInternal U)
    (hO : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0)
    (hN : ∀ i, ∀ u ∈ U i, (∀ w ∈ U i, B u w = 0) → u = 0) :
    ∃ e : {X : V →ₗ[R] V // (∀ v w, B (X v) w + B v (X w) = 0) ∧
        ∀ j, ∀ v ∈ (⨆ i : {i : ι // i ≤ j}, U i), X v ∈ ⨆ i : {i : ι // i ≤ j}, U i} ≃
        ∀ j, {Y : U j →ₗ[R] U j // ∀ x y : U j, B (Y x) y + B x (Y y) = 0},
      ∀ X j (u : U j), ((e X j).1 u : V) = X.1 u :=
  ⟨(skewFlagEquivPi hU hO hN).toEquiv, skewFlagEquivPi_apply hU hO hN⟩

theorem twisted_exact_sequence {R : Type u} [CommRing R] {I : Type w} [Preorder I]
    (F : JordanDiagram.{u, v} R I) :
    Function.Injective (JordanDiagram.TwistedAut.ofAut F) ∧
      (JordanDiagram.TwistedAut.ofAut F).range = (JordanDiagram.TwistedAut.shapeHom F).ker :=
  ⟨JordanDiagram.TwistedAut.ofAut_injective, JordanDiagram.TwistedAut.range_ofAut⟩

theorem wreath_product {R : Type u} [CommRing R] [Invertible (2 : R)] {U : Type u}
    [AddCommGroup U] [Module R U] [Module.Free R U] (BU : LinearMap.BilinForm R U)
    [Fact BU.IsSymm] (κ : Type u) [Fintype κ] [DecidableEq κ] :
    ∃ e : JordanDiagram.TwistedAut (JordanDiagram.wreathDiagram BU κ) ≃*
        (κ → SpinFactor.orthogonalGroup BU) ⋊[JordanDiagram.permAct BU κ] Equiv.Perm κ,
      ∀ t, JordanDiagram.TwistedAut.shapeHom _ t = JordanDiagram.permShape (e t).right :=
  ⟨JordanDiagram.wreathEquiv BU κ, JordanDiagram.shapeHom_eq_permShape⟩

section SpinDiagram

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type u} [AddCommGroup V]
  [Module R V] (B : LinearMap.BilinForm R V) [Fact B.IsSymm]
  {I : Type w} [Preorder I] [OrderTop I] (W : I →o Submodule R V) [Module.Free R (W ⊤)]

open SpinFactor in
theorem spin_diagram_group :
    Nonempty ((JordanDiagram.spinDiagram B W).autGroup ≃* JordanDiagram.orthStab B W) :=
  ⟨JordanDiagram.spinDiagramAutEquiv B W⟩

end SpinDiagram

end JordanDiagramCheck
