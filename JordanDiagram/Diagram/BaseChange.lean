import JordanDiagram.Diagram.Group
import JordanDiagram.Diagram.Derivation
import JordanDiagram.Algebra.BaseChange

/-!
# Scalar extension of diagrams (Lemma 2.11, Proposition 3.3, Proposition 7.9(b))

For a diagram `F : I → Jord_R` and a commutative `R`-algebra `S`, with `2` invertible in `R`,
`F.baseChange S : I → Jord_S` is `i ↦ S ⊗[R] F(i)` with the scalar-extended arrows. This is the
family `F_S = F_R ⊗_R S` of Lemma 2.11, here for one base map `R → S`.

* `baseChange_ν`: the terminal maps of `S ⊗ F` are the scalar extensions of those of `F`. They
  stay injective when `S` is flat over `R` (`baseChange_ν_injective`).
* `autBaseChange`: the group homomorphism `G_F(R) → G_F(S)`, `(gᵢ) ↦ (id ⊗ gᵢ)` (Proposition 3.3).
* `autBaseChange_injective`: if every `F(i) → S ⊗ F(i)` is injective, so is `G_F(R) → G_F(S)`
  (**Proposition 7.9(b)**).
* `derBaseChange`: the corresponding map `g_F(R) → g_F(S)` on compatible derivations
  (Proposition 3.8), additive and bracket-preserving.
-/

universe u u' v w w'

open CategoryTheory TerminallyPointed JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {I : Type w} [Category.{w'} I]
variable (S : Type u') [CommRing S] [Algebra R S]
variable (F : JordanDiagram.{u, v} R I)

/-- The scalar extension `S ⊗[R] F` of a diagram (Lemma 2.11). -/
noncomputable def baseChange : JordanDiagram.{u', max u' v} S I where
  obj i := S ⊗[R] F.obj i
  jordan _ := inferInstance
  map α := baseChangeHom S (F.map α)
  map_id i x := by
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy]
    | tmul s a => rw [baseChangeHom_tmul, F.map_id]
  map_comp α β x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    | tmul s a => rw [baseChangeHom_tmul, baseChangeHom_tmul, baseChangeHom_tmul, F.map_comp]

variable {S F}

@[simp]
theorem baseChange_map_tmul {i j : I} (α : i ⟶ j) (s : S) (a : F.obj i) :
    (F.baseChange S).map α (s ⊗ₜ a) = s ⊗ₜ F.map α a := rfl

section Aut

variable (S F) in
/-- **Proposition 3.3**: scalar extension of diagram automorphisms, a group homomorphism
`G_F(R) → G_F(S)`, `(gᵢ) ↦ (id_S ⊗ gᵢ)`. -/
noncomputable def autBaseChange : F.autGroup →* (F.baseChange S).autGroup where
  toFun g := ⟨fun i => baseChangeAut S (g.1 i), fun α x =>
    baseChangeAut_comm (fun a => autGroup_naturality g α a) x⟩
  map_one' := Subtype.ext (funext fun _ => map_one (baseChangeAut S))
  map_mul' g h := Subtype.ext (funext fun i => map_mul (baseChangeAut S) (g.1 i) (h.1 i))

@[simp]
theorem autBaseChange_tmul (g : F.autGroup) (i : I) (s : S) (a : F.obj i) :
    (autBaseChange S F g).1 i (s ⊗ₜ a) = s ⊗ₜ g.1 i a := rfl

/-- **Proposition 7.9(b)**: if every `F(i) → S ⊗[R] F(i)` is injective (e.g. `F(i)` free and
`R → S` injective), then `G_F(R) → G_F(S)` is injective. -/
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

end Aut

section Terminal

variable [TerminallyPointed I]

theorem baseChange_ν (i : I) : (F.baseChange S).ν i = baseChangeHom S (F.ν i) := rfl

/-- Scalar extension along a flat `R → S` keeps the terminal maps injective, so terminal
determination (Proposition 3.6) applies to `S ⊗ F` as well. -/
theorem baseChange_ν_injective [Module.Flat R S] (hν : ∀ i, Function.Injective (F.ν i)) (i : I) :
    Function.Injective ((F.baseChange S).ν i) :=
  baseChangeHom_injective_of_flat (F.ν i) (hν i)

end Terminal

section Der

variable (S) in
/-- Scalar extension of compatible derivations, `g_F(R) → g_F(S)` (Proposition 3.8). -/
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

end JordanDiagram
