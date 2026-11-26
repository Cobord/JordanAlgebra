module

public import JordanDiagram.Diagram.Functor
public import JordanDiagram.Diagram.Iso
public import JordanDiagram.Algebra.TwistedDescent

/-!
# Forms of a diagram and Galois cohomology

Let `L/k` be a finite Galois extension of fields (`2` invertible in `k`) and `F` a diagram over
`k`. A *form of `F` split by `L`* (`Form F L`) is a diagram `F'` over `k` with an isomorphism
`L ⊗ F' ≅ L ⊗ F`. The Galois group acts on `G_F(L)` by `σ ↦ G_F(σ)` (conjugation by `σ ⊗ 1`);
`GaloisCocycle F L` are the maps `a` with `a(σ τ) = a(σ) · σ(a(τ))`, and `H1 F L` is the set of
cocycles modulo `a ∼ c⁻¹ · a · σ(c)`.

* `Form.cocycle`: the cocycle `σ ↦ θ (σ ⊗ 1) θ⁻¹ (σ⁻¹ ⊗ 1)` of a form `θ : L ⊗ F' ≅ L ⊗ F`;
* `cohomologous_cocycle_iff`: two forms are isomorphic over `k` exactly when their cocycles are
  cohomologous (by Galois descent of isomorphisms);
* `exists_form_cocycle_eq`: every cocycle is the cocycle of a form (by twisted Galois descent);
* **`formsEquivH1`: the isomorphism classes of forms of `F` split by `L` are in bijection with
  `H¹(Gal(L/k), G_F(L))`.**
-/

@[expose] public section

noncomputable section

universe u w w'

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram

variable {k : Type u} [Field k] [Invertible (2 : k)] (L : Type u) [Field L] [Algebra k L]
variable {I : Type w} [Category.{w'} I] (F : JordanDiagram.{u, u} k I)

/-- A Galois cocycle with values in `G_F(L)`, for the action `σ ↦ G_F(σ)`. -/
structure GaloisCocycle where
  /-- The value at `σ`. -/
  toFun : (L ≃ₐ[k] L) → (F.baseChange L).autGroup
  cocycle : ∀ σ τ, toFun (σ * τ) = toFun σ * autMap F (σ : L →ₐ[k] L) (toFun τ)

variable {L F}

/-- Cohomologous cocycles: `b(σ) = c⁻¹ · a(σ) · σ(c)`. -/
def GaloisCocycle.Cohomologous (a b : GaloisCocycle L F) : Prop :=
  ∃ c : (F.baseChange L).autGroup, ∀ σ, b.toFun σ = c⁻¹ * a.toFun σ * autMap F (σ : L →ₐ[k] L) c

theorem GaloisCocycle.cohomologous_equivalence :
    Equivalence (GaloisCocycle.Cohomologous (L := L) (F := F)) where
  refl a := ⟨1, fun σ => by rw [inv_one, one_mul, map_one, mul_one]⟩
  symm {a b} := fun ⟨c, hc⟩ => ⟨c⁻¹, fun σ => by
    rw [hc, map_inv, inv_inv]
    group⟩
  trans {a b d} := fun ⟨c, hc⟩ ⟨c', hc'⟩ => ⟨c * c', fun σ => by
    rw [hc', hc, map_mul]
    group⟩

variable (L F)

instance GaloisCocycle.setoid : Setoid (GaloisCocycle L F) :=
  ⟨_, GaloisCocycle.cohomologous_equivalence⟩

/-- The Galois cohomology set `H¹(Gal(L/k), G_F(L))`. -/
def H1 : Type _ := Quotient (GaloisCocycle.setoid L F)

/-- A form of `F` split by `L`: a diagram over `k` with an isomorphism `L ⊗ F' ≅ L ⊗ F`. -/
structure Form where
  /-- The diagram. -/
  diag : JordanDiagram.{u, u} k I
  /-- The splitting isomorphism. -/
  iso : DiagramIso (diag.baseChange L) (F.baseChange L)

instance Form.setoid : Setoid (Form L F) where
  r E E' := Nonempty (DiagramIso E.diag E'.diag)
  iseqv := ⟨fun _ => ⟨DiagramIso.refl _⟩, fun ⟨θ⟩ => ⟨θ.symm⟩, fun ⟨θ⟩ ⟨θ'⟩ => ⟨θ.trans θ'⟩⟩

/-- The isomorphism classes of forms of `F` split by `L`. -/
def FormClass : Type _ := Quotient (Form.setoid L F)

variable {L F}

/-- The automorphism of `L ⊗ F` given componentwise by `twistAut`, for an isomorphism
`θ : L ⊗ F' ≅ L ⊗ F`. -/
def twistAutGroup {F' : JordanDiagram.{u, u} k I}
    (θ : DiagramIso (F'.baseChange L) (F.baseChange L)) (σ : L ≃ₐ[k] L) :
    (F.baseChange L).autGroup :=
  ⟨fun i => twistAut (θ.app i) σ, fun {i j} α x => by
    have hsymm : ∀ y, (θ.app j).symm (baseChangeHom L (F.map α) y) =
        baseChangeHom L (F'.map α) ((θ.app i).symm y) := θ.symm.naturality α
    have hθ : ∀ y, θ.app j (baseChangeHom L (F'.map α) y) =
        baseChangeHom L (F.map α) (θ.app i y) := θ.naturality α
    change θ.app j (gal _ σ ((θ.app j).symm (gal _ σ⁻¹ (baseChangeHom L (F.map α) x)))) =
      baseChangeHom L (F.map α) (θ.app i (gal _ σ ((θ.app i).symm (gal _ σ⁻¹ x))))
    rw [gal_baseChangeHom, hsymm, gal_baseChangeHom, hθ]⟩

theorem twistAutGroup_apply {F' : JordanDiagram.{u, u} k I}
    (θ : DiagramIso (F'.baseChange L) (F.baseChange L)) (σ : L ≃ₐ[k] L) (i : I) :
    (twistAutGroup θ σ).1 i = twistAut (θ.app i) σ := rfl

/-- The cocycle `σ ↦ θ (σ ⊗ 1) θ⁻¹ (σ⁻¹ ⊗ 1)` of a form. -/
def Form.cocycle (E : Form L F) : GaloisCocycle L F where
  toFun := twistAutGroup E.iso
  cocycle σ τ := Subtype.ext (funext fun i => twistAut_mul (E.iso.app i) σ τ)

/-- **Isomorphic forms have cohomologous cocycles.** -/
theorem Form.cocycle_cohomologous {E E' : Form L F} (ψ : DiagramIso E.diag E'.diag) :
    E.cocycle.Cohomologous E'.cocycle := by
  -- `χ = (L ⊗ ψ) ≫ θ'` has the cocycle of `θ'`, and differs from `θ` by `d = θ⁻¹ ≫ χ`
  let ψL : DiagramIso (E.diag.baseChange L) (E'.diag.baseChange L) :=
    ⟨fun i => baseChangeEquiv (ψ.app i), fun {i j} α x => by
      change baseChangeHom L (ψ.app j).toHom (baseChangeHom L (E.diag.map α) x) =
        baseChangeHom L (E'.diag.map α) (baseChangeHom L (ψ.app i).toHom x)
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul c a =>
        simp only [baseChangeHom_tmul, JordanEquiv.toHom_apply]
        rw [ψ.naturality]⟩
  let χ := ψL.trans E'.iso
  let d : (F.baseChange L).autGroup := DiagramIso.autEquiv _ (E.iso.symm.trans χ)
  refine ⟨d⁻¹, fun σ => Subtype.ext (funext fun i => ?_)⟩
  have h1 : twistAut (χ.app i) σ = twistAut (E'.iso.app i) σ :=
    twistAut_baseChange_trans (ψ.app i) (E'.iso.app i) σ
  have h2 : χ.app i = (E.iso.app i).trans (JordanEquiv.ofAut (d.1 i)) :=
    JordanEquiv.ext fun x => by
      change _ = χ.app i ((E.iso.app i).symm (E.iso.app i x))
      rw [JordanEquiv.symm_apply_apply]
  change twistAut (E'.iso.app i) σ = (d⁻¹)⁻¹.1 i * twistAut (E.iso.app i) σ *
    mapAut (σ : L →ₐ[k] L) ((d⁻¹).1 i)
  rw [← h1, h2, twistAut_trans_ofAut, inv_inv]
  rfl

theorem GaloisCocycle.ext {a b : GaloisCocycle L F} (h : ∀ σ, a.toFun σ = b.toFun σ) : a = b := by
  obtain ⟨a, _⟩ := a
  obtain ⟨b, _⟩ := b
  congr
  exact funext h

/-- The component at node `i` of a cocycle, a cocycle with values in `Aut(L ⊗ F(i))`. -/
def GaloisCocycle.node (a : GaloisCocycle L F) (i : I) :
    (L ≃ₐ[k] L) → jordanAut L (L ⊗[k] F.obj i) :=
  fun σ => (a.toFun σ).1 i

theorem GaloisCocycle.node_cocycle (a : GaloisCocycle L F) (i : I) (σ τ : L ≃ₐ[k] L) :
    a.node i (σ * τ) = a.node i σ * mapAut (σ : L →ₐ[k] L) (a.node i τ) :=
  congrArg (fun g : (F.baseChange L).autGroup => g.1 i) (a.cocycle σ τ)

theorem GaloisCocycle.node_naturality (a : GaloisCocycle L F) {i j : I} (α : i ⟶ j)
    (σ : L ≃ₐ[k] L) (y : L ⊗[k] F.obj i) :
    a.node j σ (baseChangeHom L (F.map α) y) = baseChangeHom L (F.map α) (a.node i σ y) :=
  (a.toFun σ).2 α y

section Galois

variable [FiniteDimensional k L] [IsGalois k L]

/-- **Forms with cohomologous cocycles are isomorphic**, by Galois descent of isomorphisms. -/
theorem Form.nonempty_iso_of_cohomologous {E E' : Form L F}
    (h : E.cocycle.Cohomologous E'.cocycle) : Nonempty (DiagramIso E.diag E'.diag) := by
  obtain ⟨c, hc⟩ := h
  -- `Ψ = θ ≫ c⁻¹ ≫ θ'⁻¹ : L ⊗ E ≅ L ⊗ E'` commutes with every `σ ⊗ 1`
  let Ψ : DiagramIso (E.diag.baseChange L) (E'.diag.baseChange L) :=
    (E.iso.trans ((DiagramIso.autEquiv _).symm c⁻¹)).trans E'.iso.symm
  have hχ : ∀ i σ, twistAut ((E.iso.app i).trans (JordanEquiv.ofAut ((c⁻¹).1 i))) σ =
      twistAut (E'.iso.app i) σ := fun i σ => by
    rw [twistAut_trans_ofAut]
    have := congrArg (fun g : (F.baseChange L).autGroup => g.1 i) (hc σ)
    change twistAut (E'.iso.app i) σ = (c⁻¹).1 i * twistAut (E.iso.app i) σ *
      mapAut (σ : L →ₐ[k] L) (c.1 i) at this
    rw [this]
    rfl
  have hΨ : ∀ i (σ : L ≃ₐ[k] L) x,
      Ψ.app i (gal (E.diag.obj i) σ x) = gal (E'.diag.obj i) σ (Ψ.app i x) := fun i σ x =>
    gal_comm_of_twistAut_eq _ (E'.iso.app i) σ (hχ i σ) x
  choose e he using fun i => exists_baseChangeEquiv_eq (Ψ.app i) (hΨ i)
  refine ⟨⟨e, fun {i j} α a => incl_injective_field (L := L) ?_⟩⟩
  change baseChangeEquiv (e j) (incl L (E.diag.map α a)) =
    baseChangeHom L (E'.diag.map α) (baseChangeEquiv (e i) (incl L a))
  rw [he, he]
  exact Ψ.naturality α (incl L a)

/-- **Isomorphism classes of forms and cohomology classes**: two forms are isomorphic over `k`
exactly when their cocycles are cohomologous. -/
theorem Form.cohomologous_cocycle_iff (E E' : Form L F) :
    E.cocycle.Cohomologous E'.cocycle ↔ Nonempty (DiagramIso E.diag E'.diag) :=
  ⟨Form.nonempty_iso_of_cohomologous, fun ⟨ψ⟩ => Form.cocycle_cohomologous ψ⟩

/-- The form defined by a cocycle, by twisted Galois descent at every node. -/
def GaloisCocycle.form (a : GaloisCocycle L F) : Form L F where
  diag :=
    { obj := fun i => twistForm (a.node i)
      map := fun α => twistMap _ _ (F.map α) (a.node_naturality α)
      map_id := fun i x => Subtype.ext ((F.baseChange L).map_id i (x : L ⊗[k] F.obj i))
      map_comp := fun α β x => Subtype.ext ((F.baseChange L).map_comp α β x.1) }
  iso := ⟨fun i => twistIso (a.node i) (a.node_cocycle i), fun {i j} α z =>
    twistIso_naturality (a.node i) (a.node_cocycle i) (a.node j) (a.node_cocycle j) (F.map α)
      (a.node_naturality α) z⟩

/-- **Every cocycle is the cocycle of a form.** -/
theorem GaloisCocycle.form_cocycle (a : GaloisCocycle L F) : a.form.cocycle = a :=
  GaloisCocycle.ext fun σ => Subtype.ext (funext fun i =>
    twistAut_twistIso (a.node i) (a.node_cocycle i) σ)

variable (L F) in
/-- **Forms and Galois cohomology**: the isomorphism classes of forms of `F` split by `L` are in
bijection with `H¹(Gal(L/k), G_F(L))`, by `θ ↦ (σ ↦ θ (σ ⊗ 1) θ⁻¹ (σ⁻¹ ⊗ 1))`. -/
def formsEquivH1 : FormClass L F ≃ H1 L F :=
  Equiv.ofBijective
    (Quotient.map Form.cocycle fun _ _ ⟨ψ⟩ => Form.cocycle_cohomologous ψ)
    ⟨fun x y => Quotient.inductionOn₂ x y fun E E' h =>
        Quotient.sound (Form.nonempty_iso_of_cohomologous (Quotient.exact h)),
      fun x => Quotient.inductionOn x fun a => ⟨⟦a.form⟧, by
        change ⟦a.form.cocycle⟧ = _
        rw [GaloisCocycle.form_cocycle]⟩⟩

theorem formsEquivH1_mk (E : Form L F) :
    formsEquivH1 L F ⟦E⟧ = (⟦E.cocycle⟧ : H1 L F) := rfl

end Galois

end JordanDiagram
