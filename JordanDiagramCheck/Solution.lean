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
      ∀ h : jordanAut R F.TerminalJordanAlgebra, h ∈ (JordanDiagram.ev F).range ↔
        ∀ i, h '' F.image i = F.image i := by
  refine ⟨JordanDiagram.ev_injective hν, fun h => ?_⟩
  rw [JordanDiagram.range_ev hν, JordanDiagram.mem_stabImages]

theorem compatible_derivations (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) :
    Function.Injective (JordanDiagram.evDer F) ∧
      Set.range (JordanDiagram.evDer F) =
        {d : JordanDerivation R F.TerminalJordanAlgebra | ∀ i, ∀ y ∈ F.image i, d y ∈ F.image i} :=
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
      {h : F.TerminalJordanAlgebra ≃ⱼ[R] F'.TerminalJordanAlgebra // ∀ i, h '' F.image i = F'.image i}) :=
  ⟨JordanDiagram.DiagramIso.terminalEquiv hν hν'⟩

theorem finite_detector (F : JordanDiagram.{u, v} R I)
    (hν : ∀ i, Function.Injective (F.ν i)) {X : Set F.TerminalJordanAlgebra} [Finite X]
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

theorem comparison_subgroups
    (h : ∀ i, Function.Injective (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)) (H : Subgroup F.autGroup) :
    Nonempty (H ≃* H.map (JordanDiagram.autBaseChange S F)) ∧
      Nat.card (H.map (JordanDiagram.autBaseChange S F)) = Nat.card H :=
  ⟨⟨JordanDiagram.subgroupEquivMap h H⟩, JordanDiagram.card_map_autBaseChange h H⟩

theorem square_zero_automorphisms {K : Type u} [CommRing K] (G : JordanDiagram.{u, v} K I) :
    (∀ e : K, e * e = 0 → ∀ D : G.derAlgebra,
      ∃ g : G.autGroup, ∀ i x, g.1 i x = x + e • D.1 i x) ∧
    (∀ e e' : K, e * e = 0 → e' * e' = 0 → ∀ (D D' : G.derAlgebra) (g g' : G.autGroup),
      (∀ i x, g.1 i x = x + e • D.1 i x) → (∀ i x, g'.1 i x = x + e' • D'.1 i x) →
        ∀ i x, (g * g' * g⁻¹ * g'⁻¹).1 i x = x + (e * e') • (⁅D, D'⁆ : G.derAlgebra).1 i x) := by
  refine ⟨fun e he D => ⟨JordanDiagram.sqZeroAutGroup G e he D, fun _ _ => rfl⟩,
    fun e e' he he' D D' g g' hg hg' i x => ?_⟩
  obtain rfl : g = JordanDiagram.sqZeroAutGroup G e he D :=
    Subtype.ext (funext fun i => jordanAut.ext (hg i))
  obtain rfl : g' = JordanDiagram.sqZeroAutGroup G e' he' D' :=
    Subtype.ext (funext fun i => jordanAut.ext (hg' i))
  rw [JordanDiagram.sqZeroAutGroup_commutator]
  rfl

theorem lie_algebra_dual_numbers (S : Type u') [CommRing S] [Algebra R S] :
    ∃ e : (F.baseChange S).derAlgebra ≃+
        Additive (JordanDiagram.autMap F (TrivSqZeroExt.fstHom R S S)).ker,
      ∀ D i x, (e D).toMul.1.1 i x =
        x + (DualNumber.eps : DualNumber S) •
          (JordanDiagram.derMap F (TrivSqZeroExt.inlAlgHom R S S) D).1 i x :=
  ⟨JordanDiagram.dualAutEquiv F S, JordanDiagram.dualAutEquiv_apply F S⟩

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

theorem zHalf_hom (R : Type u) [CommRing R] :
    Subsingleton (Localization.Away (2 : ℤ) →+* R) ∧
      (Nonempty (Localization.Away (2 : ℤ) →+* R) ↔ IsUnit (2 : R)) :=
  ⟨zHalf_ringHom_subsingleton R, nonempty_zHalf_ringHom_iff R⟩

theorem octonion_norm_coefficients {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]
    {a b c : R} (x : Octonion R a b (-c)) :
    x * star x = Octonion.scalarEmbed (∑ i : Fin 8,
      ![1, -a, -b, a * b, -c, a * c, b * c, -(a * b * c)] i *
        ![x.1.re, x.1.imI, x.1.imJ, x.1.imK, x.2.re, x.2.imI, x.2.imJ, x.2.imK] i ^ 2) :=
  Octonion.mul_star_self_eq_diag x

theorem octonion_norm_coefficients_pos {R : Type u} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : a < 0) (hb : b < 0) (hc : c < 0) (i : Fin 8) :
    0 < ![1, -a, -b, a * b, -c, a * c, b * c, -(a * b * c)] i :=
  Octonion.normCoeff_pos ha hb hc i

theorem shape_twisted_group {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]
    [TerminallyPointed I] (F : JordanDiagram.{u, v} R I) :
    Function.Injective (JordanDiagram.ShapeTwistedAut.ofAut F) ∧
      (JordanDiagram.ShapeTwistedAut.ofAut F).range =
        (JordanDiagram.ShapeTwistedAut.shapeHom F).ker ∧
      (∀ p, p ∈ JordanDiagram.ShapeTwistedAut.terminalPairs F ↔
        ∀ i, p.2 '' F.image i = F.image (p.1.functor.obj i)) ∧
      ((∀ i, Function.Injective (F.ν i)) →
        ∃ e : JordanDiagram.ShapeTwistedAut F ≃* JordanDiagram.ShapeTwistedAut.terminalPairs F,
          ∀ a, (e a : JordanDiagram.ShapeAut I × jordanAut R F.TerminalJordanAlgebra) =
            (a.shape, JordanDiagram.ShapeTwistedAut.topAut a)) :=
  ⟨JordanDiagram.ShapeTwistedAut.ofAut_injective, JordanDiagram.ShapeTwistedAut.range_ofAut,
    fun _ => JordanDiagram.ShapeTwistedAut.mem_terminalPairs,
    fun hν => ⟨JordanDiagram.ShapeTwistedAut.terminalEquiv hν, fun _ => rfl⟩⟩

theorem minkowski {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ} (hm : 3 ≤ m) :
    (∀ g : Matrix n n ℤ, (∀ a b, (m : ℤ) ∣ (g - 1) a b) → ∀ r ≠ 0, g ^ r = 1 → g = 1) ∧
      ∀ H : Subgroup (GL n ℤ), Finite H →
        Set.InjOn (Units.map ((Int.castRingHom (ZMod m)).mapMatrix (m := n)).toMonoidHom :
          GL n ℤ →* GL n (ZMod m)) (H : Set (GL n ℤ)) :=
  ⟨fun _ hg _ hr hgr => Matrix.eq_one_of_pow_eq_one_of_modEq hm hg hr hgr,
    fun H _ => Matrix.injOn_reduce hm H⟩

theorem spinFactor_formallyReal_iff {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] {V : Type v} [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm) :
    @IsFormallyReal R (SpinFactor R V B) _ (SpinFactor.jordanAlgebra B hB) ↔
      B.toQuadraticMap.PosDef :=
  SpinFactor.isFormallyReal_iff_posDef B hB

theorem fraction_field_order (R : Type u) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    IsDomain R ∧ IsStrictOrderedRing (FractionRing R) ∧
      (∀ r s : R, algebraMap R (FractionRing R) r ≤ algebraMap R (FractionRing R) s ↔ r ≤ s) ∧
      ∀ o₁ o₂ : LinearOrder (FractionRing R),
        @IsStrictOrderedRing (FractionRing R) _ o₁.toPartialOrder →
        @IsStrictOrderedRing (FractionRing R) _ o₂.toPartialOrder →
        (∀ r s : R, r ≤ s → o₁.le (algebraMap R _ r) (algebraMap R _ s)) →
        (∀ r s : R, r ≤ s → o₂.le (algebraMap R _ r) (algebraMap R _ s)) →
        ∀ x y, o₁.le x y ↔ o₂.le x y :=
  ⟨inferInstance, inferInstance, fun _ _ => FractionRing.algebraMap_le_iff,
    fun o₁ o₂ h₁ h₂ m₁ m₂ x y => (FractionRing.le_iff_of_order o₁ h₁ m₁ x y).trans
      (FractionRing.le_iff_of_order o₂ h₂ m₂ x y).symm⟩

theorem subgroup_at_terminal {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I]
    [TerminallyPointed I] (F : JordanDiagram.{u, v} R I) (L : AddSubgroup F.TerminalJordanAlgebra) :
    (∀ g : F.autGroup, g.1 top '' (L : Set F.TerminalJordanAlgebra) = L ↔
      ∀ i, g.1 i '' (L.comap (F.ν i : F.obj i →+ F.TerminalJordanAlgebra) : Set (F.obj i)) =
        L.comap (F.ν i : F.obj i →+ F.TerminalJordanAlgebra)) ∧
      (∀ c : ℕ, (∀ y : F.TerminalJordanAlgebra, ∃ k : ℕ, (c ^ k) • y ∈ L) →
        ∀ i (x : F.obj i), ∃ k : ℕ, (c ^ k) • x ∈ L.comap (F.ν i : F.obj i →+ F.TerminalJordanAlgebra)) ∧
      (Module.Finite ℤ L → ∀ i, Function.Injective (F.ν i) →
        Module.Finite ℤ (L.comap (F.ν i : F.obj i →+ F.TerminalJordanAlgebra))) :=
  ⟨JordanDiagram.image_top_eq_iff,
    fun _ hL i x => JordanDiagram.exists_pow_smul_mem_nodePreimage hL i x,
    fun _ _ hν => JordanDiagram.finite_nodePreimage hν⟩

theorem octonion_nonsingular {R : Type u} [CommRing R] [Invertible (2 : R)] [StarRing R]
    [TrivialStar R] (a b c : R) :
    Function.Bijective (Octonion.innerProduct : LinearMap.BilinForm R (Octonion R a b (-c))) ↔
      IsUnit a ∧ IsUnit b ∧ IsUnit c :=
  Octonion.bijective_innerProduct_iff

theorem hermitian_two {R : Type u} [CommRing R] [Invertible (2 : R)] [StarRing R] [TrivialStar R]
    (a b c : R) :
    (∀ M : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2),
      Octonion.ofSymmetricMatricesTwo M = SpinFactor.mk _
        (M.val 0 1, ⅟(2 : R) * ((M.val 0 0).1.re - (M.val 1 1).1.re))
        (⅟(2 : R) * ((M.val 0 0).1.re + (M.val 1 1).1.re))) ∧
    (∀ (r : R) (M : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2)),
      Octonion.ofSymmetricMatricesTwo (r • M) = r • Octonion.ofSymmetricMatricesTwo M) ∧
    (∀ M N : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2),
      Octonion.ofSymmetricMatricesTwo (M * N) =
        Octonion.ofSymmetricMatricesTwo M * Octonion.ofSymmetricMatricesTwo N) ∧
    Function.Bijective
      (Octonion.ofSymmetricMatricesTwo (R := R) (a := a) (b := b) (c := c)) ∧
    (∀ (x y : Octonion R a b c) (α β : R),
      Octonion.hermitianTwoBilin (x, α) (y, β) = Octonion.innerProduct x y + α * β) ∧
    (∀ k : ℕ, (1 : Octonion R a b c) ∈ Octonion.cdStage k ∧
      (∀ x ∈ Octonion.cdStage (a := a) (b := b) (c := c) k, ∀ y ∈ Octonion.cdStage k,
        x * y ∈ Octonion.cdStage k) ∧
      ∀ x ∈ Octonion.cdStage (a := a) (b := b) (c := c) k, star x ∈ Octonion.cdStage k) ∧
    ∀ (k : ℕ) (M : HermitianOctonionMatrix (R := R) (a := a) (b := b) (c := c) (n := Fin 2)),
      (∀ i j, M.val i j ∈ Octonion.cdStage k) ↔
        (Octonion.ofSymmetricMatricesTwo M).1.1 ∈ Octonion.cdStage k :=
  ⟨Octonion.ofSymmetricMatricesTwo_apply, Octonion.ofSymmetricMatricesTwo_smul,
    map_mul Octonion.ofSymmetricMatricesTwo, Octonion.ofSymmetricMatricesTwo.bijective,
    Octonion.hermitianTwoBilin_apply,
    fun k => ⟨Octonion.one_mem_cdStage k, fun _ hx _ hy => Octonion.mul_mem_cdStage hx hy,
      fun _ hx => Octonion.star_mem_cdStage hx⟩,
    Octonion.forall_mem_cdStage_iff⟩

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
  refine ⟨fun H _ => ?_, fun hfin K => ?_⟩
  · obtain ⟨L, hL, hle⟩ := ZHalf.exists_isFGSpanning_le_stabilizer ρ H
    exact ⟨⟨L, hL.fg, hL.span_eq_top, fun g hg => hle hg⟩, ZHalf.card_le hρ H,
      ZHalf.exists_maximal_finite hρ H⟩
  · have e : (fun K : Subgroup G => ∃ L, ZHalf.IsFGSpanning L ∧ K = ZHalf.stabilizer ρ L) =
        fun K : Subgroup G => ∃ L : Submodule ℤ M, L.FG ∧
          Submodule.span ZHalf (L : Set M) = ⊤ ∧ K = ZHalf.stabilizer ρ L := by
      funext K
      apply propext
      constructor
      · rintro ⟨L, hL, rfl⟩
        exact ⟨L, hL.fg, hL.span_eq_top, rfl⟩
      · rintro ⟨L, h1, h2, rfl⟩
        exact ⟨L, ⟨h1, h2⟩, rfl⟩
    rw [ZHalf.maximal_finite_iff (fun L hL => hfin L hL.fg hL.span_eq_top) K, e]

theorem finite_stabilizers_of_form {M : Type u} [AddCommGroup M] [Module ZHalf M]
    [Module.Finite ZHalf M] [Module.Free ZHalf M] {G : Type v} [Group G]
    (ρ : G →* (M ≃ₗ[ZHalf] M)) (hρ : Function.Injective ρ) (β : M →+ M →+ ℚ)
    (hpos : ∀ x, x ≠ 0 → 0 < β x x) (hinv : ∀ g x y, β (ρ g x) (ρ g y) = β x y) :
    (∀ L : Submodule ℤ M, L.FG → Submodule.span ZHalf (L : Set M) = ⊤ →
        Finite (ZHalf.stabilizer ρ L)) ∧
      ∀ K : Subgroup G, Maximal (fun K : Subgroup G => Finite K) K ↔
        Maximal (fun K : Subgroup G => ∃ L : Submodule ℤ M, L.FG ∧
          Submodule.span ZHalf (L : Set M) = ⊤ ∧ K = ZHalf.stabilizer ρ L) K := by
  have hfin : ∀ L : Submodule ℤ M, L.FG → Submodule.span ZHalf (L : Set M) = ⊤ →
      Finite (ZHalf.stabilizer ρ L) := fun L h1 h2 =>
    ZHalf.finite_stabilizer_of_form hρ β hpos hinv ⟨h1, h2⟩
  exact ⟨hfin, (finite_subgroups ρ hρ).2 hfin⟩

open Matrix in
theorem finite_at_two {M : Type u} [AddCommMonoid M] [Module ZHalf M] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ZHalf M) {G : Type v} [Group G] (ρ : G →* (M ≃ₗ[ZHalf] M))
    (hρ : Function.Injective ρ) (β : LinearMap.BilinForm ZHalf M)
    (hinv : ∀ g x y, β (ρ g x) (ρ g y) = β x y) (hpos : ∀ x, x ≠ 0 → 0 < ZHalf.toRat (β x x))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun i j => ((ZHalf.toRat (β (b i) (b j)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite G :=
  ZHalf.finite_of_form b hρ β hinv hpos h2

open Matrix in
theorem spin_diagram_finite_at_two {V : Type} [AddCommGroup V] [Module ZHalf V]
    (B : LinearMap.BilinForm ZHalf V) [Fact B.IsSymm] {I : Type w} [Preorder I] [OrderTop I]
    (W : I →o Submodule ZHalf V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ZHalf (W ⊤)) (hpos : ∀ v, v ≠ 0 → 0 < ZHalf.toRat (B v v))
    (h2 : ∀ v : ι → ℚ_[2], v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun i j => ((ZHalf.toRat (B (b i) (b j)) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (JordanDiagram.spinDiagram B W).autGroup :=
  JordanDiagram.finite_spinDiagram B W b hpos h2

open Matrix in
theorem flag_finite_at_two {V : Type} [AddCommGroup V] [Module ZHalf V]
    (B : LinearMap.BilinForm ZHalf V) {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (U : ι → Submodule ZHalf V) (hU : DirectSum.IsInternal U)
    (hO : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ w ∈ U j, B u w = 0)
    (hN : ∀ i, ∀ u ∈ U i, (∀ w ∈ U i, B u w = 0) → u = 0) {κ : ι → Type} [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)] (b : ∀ j, Module.Basis (κ j) ZHalf (U j))
    (hpos : ∀ v, v ≠ 0 → 0 < ZHalf.toRat (B v v))
    (h2 : ∀ j (v : κ j → ℚ_[2]), v ≠ 0 →
      v ⬝ᵥ (Matrix.of fun k k' => ((ZHalf.toRat (B (b j k) (b j k')) : ℚ) : ℚ_[2])) *ᵥ v ≠ 0) :
    Finite (SpinFactor.stabFamily B (fun j => ⨆ i : {i : ι // i ≤ j}, U i)) :=
  JordanDiagram.finite_stabFlag B hU hO hN b hpos h2

theorem forms_galois_cohomology {k L : Type u} [Field k] [Invertible (2 : k)] [Field L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] {I : Type w} [Category.{w'} I]
    (F : JordanDiagram.{u, u} k I) :
    ∃ e : JordanDiagram.FormClass L F ≃ JordanDiagram.H1 L F,
      (∀ E : JordanDiagram.Form L F, e ⟦E⟧ = ⟦E.cocycle⟧) ∧
      (∀ (E : JordanDiagram.Form L F) (σ : L ≃ₐ[k] L) (i : I) (x : L ⊗[k] F.obj i),
        (E.cocycle.toFun σ).1 i x = E.iso.app i
          (TensorProduct.map (σ : L →ₐ[k] L).toLinearMap LinearMap.id ((E.iso.app i).symm
            (TensorProduct.map ((σ⁻¹ : L ≃ₐ[k] L) : L →ₐ[k] L).toLinearMap LinearMap.id x)))) ∧
      ∀ E E' : JordanDiagram.Form L F,
        E.cocycle.Cohomologous E'.cocycle ↔ Nonempty (JordanDiagram.DiagramIso E.diag E'.diag) :=
  ⟨JordanDiagram.formsEquivH1 L F, JordanDiagram.formsEquivH1_mk, fun _ _ _ _ => rfl,
    JordanDiagram.Form.cohomologous_cocycle_iff⟩

theorem diagram_faithful {I : Type w} [Category.{w'} I] [TerminallyPointed I]
    (F : JordanDiagram.{0, v} ZHalf I) :
    Function.Injective F.nodesRep ∧
      ((∀ i, Function.Injective (F.ν i)) → Function.Injective F.terminalRep) :=
  ⟨F.nodesRep_injective, F.terminalRep_injective⟩

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
      (JordanDiagram.restrictionFunctor.{u, v, w, w'} R).toPseudofunctor').IsFibered :=
  ⟨JordanDiagram.restrictFunctor_id I, JordanDiagram.restrictFunctor_comp p p',
    JordanDiagram.restrictFunctor_comp_baseChangeFunctor S p', inferInstance⟩

theorem diagram_pseudofunctor :
    (∀ X : TPCat.{w, w'}ᵒᵖ × CommAlgCat.{u} ZHalf,
      (JordanDiagram.diagramPseudofunctor.obj ⟨X⟩ : Cat.{max u w, max (u + 1) w w'}) =
        Cat.of (JordanDiagram.{u, u} X.2 X.1.unop.carrier)) ∧
    ∀ {X Y : TPCat.{w, w'}ᵒᵖ × CommAlgCat.{u} ZHalf} (f : X ⟶ Y),
      (JordanDiagram.diagramPseudofunctor.map f.toLoc).toFunctor = JordanDiagram.diagramMap f :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem base_change_opfibration (I : Type w) [Category.{w'} I]
    (a : Pseudofunctor.Grothendieck (JordanDiagram.baseChangePseudofunctor.{u, w, w'} I))
    {S : CommAlgCat.{u} ZHalf} (f : a.base ⟶ S) :
    ∃ (b : Pseudofunctor.Grothendieck (JordanDiagram.baseChangePseudofunctor I)) (φ : a ⟶ b),
      (Pseudofunctor.Grothendieck.forget _).IsStronglyCocartesian f φ :=
  JordanDiagram.exists_isStronglyCocartesian_baseChange I a f

theorem diagram_representable {k : Type u} [CommRing k] [Invertible (2 : k)] {I : Type w}
    [Category.{w'} I] (F : JordanDiagram.{u, v} k I) [∀ i, Module.Free k (F.obj i)]
    [∀ i, Module.Finite k (F.obj i)] :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra k B)
      (e : ∀ (S : Type u') [CommRing S] [Algebra k S], (B →ₐ[k] S) ≃ (F.baseChange S).autGroup),
      (∀ (S T : Type u') [CommRing S] [Algebra k S] [CommRing T] [Algebra k T] (χ : S →ₐ[k] T)
        (f : B →ₐ[k] S), e T (χ.comp f) = JordanDiagram.autMap F χ (e S f)) ∧
      (Finite I → Algebra.FiniteType k B) ∧
      ∃ (A : Type (max u v w)) (_ : CommRing A) (_ : Algebra k A)
        (eGL : ∀ (S : Type u') [CommRing S] [Algebra k S],
          (A →ₐ[k] S) ≃ ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i)
        (π : A →ₐ[k] B), Function.Surjective π ∧
        ∀ (S : Type u') [CommRing S] [Algebra k S] (f : B →ₐ[k] S) (i : I),
          eGL S (f.comp π) i = ((e S f).1 i : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) :=
  JordanDiagram.representable.{u, u'} F

open AlgebraicGeometry MonObj in
theorem diagram_group_scheme {k : Type u} [CommRing k] [Invertible (2 : k)] {I : Type u}
    [Category.{w'} I] (F : JordanDiagram.{u, u} k I) [∀ i, Module.Free k (F.obj i)]
    [∀ i, Module.Finite k (F.obj i)] :
    ∃ (B A : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : CommRing A) (_ : Algebra k A)
      (_ : GrpObj (JordanDiagram.specOver (k := k) B))
      (_ : GrpObj (JordanDiagram.specOver (k := k) A))
      (eB : yonedaGrpObj (JordanDiagram.specOver (k := k) B) ≅ JordanDiagram.pointsFunctor F)
      (eA : yonedaGrpObj (JordanDiagram.specOver (k := k) A) ≅ JordanDiagram.glPoints F)
      (j : JordanDiagram.specOver (k := k) B ⟶ JordanDiagram.specOver A),
      IsMonHom j ∧ IsClosedImmersion j.left ∧
      (∀ (T : Over (JordanDiagram.baseScheme k)) (x : T ⟶ JordanDiagram.specOver (k := k) B),
        (eA.hom.app (Opposite.op T)).hom (x ≫ j) =
          JordanDiagram.components F (JordanDiagram.sectionsAlg T)
            ((eB.hom.app (Opposite.op T)).hom x)) ∧
      (Finite I → Algebra.FiniteType k B) :=
  JordanDiagram.groupScheme F

end JordanDiagramCheck
