module

public import JordanDiagram.Diagram.Group
public import JordanDiagram.Diagram.Derivation
public import JordanDiagram.Algebra.BaseChange
public import JordanDiagram.Algebra.Tower

/-!
# Scalar extension of diagrams

For a diagram `F : I → Jord_R` and a commutative `R`-algebra `S`, with `2` invertible in `R`,
`F.baseChange S : I → Jord_S` is `i ↦ S ⊗[R] F(i)` with the scalar-extended arrows. This is the
scalar-extension family `F_S = F_R ⊗_R S`, here for one base map `R → S`.

* `baseChange_ν`: the terminal maps of `S ⊗ F` are the scalar extensions of those of `F`. They
  stay injective when `S` is flat over `R` (`baseChange_ν_injective`).
* `autBaseChange`: the group homomorphism `G_F(R) → G_F(S)`, `(gᵢ) ↦ (id ⊗ gᵢ)`.
* `autBaseChange_injective`: if every `F(i) → S ⊗ F(i)` is injective, so is `G_F(R) → G_F(S)`.
* `derBaseChange`: the corresponding map `g_F(R) → g_F(S)` on compatible derivations,
  additive and bracket-preserving.
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory TerminallyPointed JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]
variable (S : Type u') [CommRing S] [Algebra R S]
variable (F : JordanDiagram.{u, v} R I)

/-- The scalar extension `S ⊗[R] F` of a diagram. Reducible, so that its nodes are
seen as the tensor products `S ⊗[R] F(i)` by rewriting and instance search. -/
@[reducible] noncomputable def baseChange : JordanDiagram.{u', max u' v} S I where
  obj i := S ⊗[R] F.obj i
  jordan _ := inferInstance
  map α := baseChangeHom S (F.map α)
  map_id i x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, hx, hy]
    | tmul s a => rw [baseChangeHom_tmul, F.map_id]
  map_comp α β x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    | tmul s a => rw [baseChangeHom_tmul, baseChangeHom_tmul, baseChangeHom_tmul, F.map_comp]

variable {S F}

@[simp]
theorem baseChange_map_tmul {i j : I} (α : i ⟶ j) (s : S) (a : F.obj i) :
    (F.baseChange S).map α (s ⊗ₜ a) = s ⊗ₜ F.map α a := rfl

section Aut

variable (S F) in
/-- Scalar extension of diagram automorphisms, a group homomorphism
`G_F(R) → G_F(S)`, `(gᵢ) ↦ (id_S ⊗ gᵢ)`. -/
noncomputable def autBaseChange : F.autGroup →* (F.baseChange S).autGroup where
  toFun g := ⟨fun i => baseChangeAut S (g.1 i), fun α x =>
    baseChangeAut_comm (fun a => autGroup_naturality g α a) x⟩
  map_one' := Subtype.ext (funext fun _ => map_one (baseChangeAut S))
  map_mul' g h := Subtype.ext (funext fun i => map_mul (baseChangeAut S) (g.1 i) (h.1 i))

@[simp]
theorem autBaseChange_tmul (g : F.autGroup) (i : I) (s : S) (a : F.obj i) :
    (autBaseChange S F g).1 i (s ⊗ₜ a) = s ⊗ₜ g.1 i a := rfl

/-- **Injectivity of scalar extension**: if every `F(i) → S ⊗[R] F(i)` is injective (e.g. `F(i)`
free and `R → S` injective), then `G_F(R) → G_F(S)` is injective. -/
theorem autBaseChange_injective
    (h : ∀ i, Function.Injective (fun a : F.obj i => (1 : S) ⊗ₜ[R] a)) :
    Function.Injective (autBaseChange S F) := by
  intro g g' hgg'
  apply Subtype.ext
  funext i
  ext a
  apply h i
  have := congrArg (fun k : (F.baseChange S).autGroup => k.1 i ((1 : S) ⊗ₜ a)) hgg'
  exact this

/-- **Image of scalar extension**: if every `a ↦ 1 ⊗ a : F(i) → S ⊗[R] F(i)` is injective
(e.g. `F(i)` free and `R → S` injective), then, identifying `F(i)` with its image `1 ⊗ F(i)`,
the image of `G_F(R) → G_F(S)` consists of the automorphisms preserving every `F(i)` setwise. -/
theorem range_autBaseChange (hι : ∀ i, Function.Injective (incl (A := F.obj i) S)) :
    Set.range (autBaseChange S F) =
      {g | ∀ i, g.1 i '' Set.range (incl (A := F.obj i) S) = Set.range (incl S)} := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩ i
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨h.1 i a, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨incl S ((h.1 i)⁻¹ b), ⟨_, rfl⟩, ?_⟩
      change incl S (h.1 i ((h.1 i)⁻¹ b)) = incl S b
      rw [jordanAut.apply_inv_self]
  · intro hg
    have pres : ∀ i, PreservesIncl (g.1 i) := fun i a => by
      have hmem : g.1 i (incl S a) ∈ g.1 i '' Set.range (incl S) := ⟨incl S a, ⟨a, rfl⟩, rfl⟩
      rw [hg i] at hmem
      obtain ⟨b, hb⟩ := hmem
      exact ⟨b, hb.symm⟩
    have pres' : ∀ i, PreservesIncl (g.1 i)⁻¹ := fun i a => by
      have hmem : incl S a ∈ g.1 i '' Set.range (incl S) := (hg i).symm ▸ ⟨a, rfl⟩
      obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hmem
      exact ⟨b, by rw [← hb, jordanAut.inv_apply_self]⟩
    refine ⟨⟨fun i => descendAut (hι i) (g.1 i) (pres i) (pres' i), ?_⟩, ?_⟩
    · intro i j α a
      apply hι j
      rw [incl_descendAut]
      have h1 : incl S (F.map α a) = (F.baseChange S).map α (incl S a) := rfl
      have h2 : incl S (F.map α (descendAut (hι i) (g.1 i) (pres i) (pres' i) a)) =
          (F.baseChange S).map α (incl S (descendAut (hι i) (g.1 i) (pres i) (pres' i) a)) := rfl
      rw [h1, autGroup_naturality g α, h2, incl_descendAut]
    · exact Subtype.ext (funext fun i => baseChangeAut_descendAut (hι i) _ _ _)

/-- If every `a ↦ 1 ⊗ a : F(i) → S ⊗[R] F(i)` is injective, `G_F(R)` is isomorphic to the
subgroup of `G_F(S)` preserving every `F(i)`. -/
noncomputable def autGroupEquivPreserving (hι : ∀ i, Function.Injective (incl (A := F.obj i) S)) :
    F.autGroup ≃* (autBaseChange S F).range :=
  MonoidHom.ofInjective (autBaseChange_injective hι)

end Aut

section Terminal

variable [TerminallyPointed I]

theorem baseChange_ν (i : I) : (F.baseChange S).ν i = baseChangeHom S (F.ν i) := rfl

/-- Scalar extension along a flat `R → S` keeps the terminal maps injective, so terminal
determination applies to `S ⊗ F` as well. -/
theorem baseChange_ν_injective [Module.Flat R S] (hν : ∀ i, Function.Injective (F.ν i)) (i : I) :
    Function.Injective ((F.baseChange S).ν i) :=
  baseChangeHom_injective_of_flat (F.ν i) (hν i)

end Terminal

section Der

variable (S) in
/-- Scalar extension of compatible derivations, `g_F(R) → g_F(S)`. -/
noncomputable def derBaseChange (D : F.derAlgebra) : (F.baseChange S).derAlgebra :=
  ⟨fun i => baseChangeDer S (D.1 i), fun α x => baseChangeDer_comm (fun a => D.2 α a) x⟩

@[simp]
theorem derBaseChange_tmul (D : F.derAlgebra) (i : I) (s : S) (a : F.obj i) :
    (derBaseChange S D).1 i (s ⊗ₜ a) = s ⊗ₜ D.1 i a := rfl

theorem derBaseChange_add (D E : F.derAlgebra) :
    derBaseChange S (D + E) = derBaseChange S D + derBaseChange S E :=
  Subtype.ext (funext fun i => baseChangeDer_add (D.1 i) (E.1 i))

theorem derBaseChange_lie (D E : F.derAlgebra) :
    derBaseChange S ⁅D, E⁆ = ⁅derBaseChange S D, derBaseChange S E⁆ :=
  Subtype.ext (funext fun i => baseChangeDer_lie (D.1 i) (E.1 i))

end Der

section Tower

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Invertible (2 : S)]

theorem cancelJordanEquiv_symm_baseChangeHom {A B : Type*} [JordanAlgebra R A] [JordanAlgebra R B]
    (f : A →ₙₐ[R] B) (x : T ⊗[R] A) :
    (cancelJordanEquiv R S T B).symm (baseChangeHom T f x) =
      baseChangeHom T (baseChangeHom S f) ((cancelJordanEquiv R S T A).symm x) := by
  apply (cancelJordanEquiv R S T B).injective
  rw [JordanEquiv.apply_symm_apply, cancelJordanEquiv_baseChangeHom, JordanEquiv.apply_symm_apply]

variable (S T F) in
/-- **Functoriality in the base**: `G_F(S) → G_F(T)` for `R → S → T`,
`(gᵢ) ↦ (β ∘ (id_T ⊗ gᵢ) ∘ β⁻¹)` with `β : T ⊗[S] (S ⊗[R] F(i)) ≃ T ⊗[R] F(i)`. -/
noncomputable def autTowerDiagram : (F.baseChange S).autGroup →* (F.baseChange T).autGroup where
  toFun g := ⟨fun i => autTower S T (g.1 i), by
    intro i j α x
    change cancelJordanEquiv R S T (F.obj j) (baseChangeAut T (g.1 j)
        ((cancelJordanEquiv R S T (F.obj j)).symm (baseChangeHom T (F.map α) x))) =
      baseChangeHom T (F.map α) (cancelJordanEquiv R S T (F.obj i) (baseChangeAut T (g.1 i)
        ((cancelJordanEquiv R S T (F.obj i)).symm x)))
    rw [cancelJordanEquiv_symm_baseChangeHom,
      baseChangeAut_comm (fun a => autGroup_naturality g α a), cancelJordanEquiv_baseChangeHom]⟩
  map_one' := Subtype.ext (funext fun _ => map_one (autTower S T))
  map_mul' g h := Subtype.ext (funext fun i => map_mul (autTower S T) (g.1 i) (h.1 i))

/-- **Compatibility of base extensions**: `G_F(R) → G_F(S) → G_F(T)` is `G_F(R) → G_F(T)`. -/
theorem autTowerDiagram_comp_autBaseChange :
    (autTowerDiagram S F T).comp (autBaseChange S F) = autBaseChange T F :=
  MonoidHom.ext fun g => Subtype.ext (funext fun i => autTower_baseChangeAut (g.1 i))

end Tower

end JordanDiagram
