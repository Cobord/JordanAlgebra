import JordanDiagram.Diagram.Group
import JordanDiagram.Diagram.Derivation
import JordanDiagram.Diagram.Iso
import JordanDiagram.Algebra.SpinFactor

/-!
# Diagrams of spin factors (Section 5)

Let `I` be a preorder with a greatest element `⊤`, regarded as a category with one arrow `i ⟶ j`
when `i ≤ j`. A monotone family `W : I →o Submodule R V` of submodules of a module `V` with a
symmetric bilinear form `B` gives the *spin-factor diagram* (Definition 5.3)
`i ↦ J(Wᵢ, B|_{Wᵢ})`, with the inclusions `J(Wᵢ, B) ↪ J(Wⱼ, B)` as arrows (`spinDiagram`).
The paper's case is `I = P⁺ = WithTop P`, with `W₊ = V`.

* `spinDiagram_ν_injective`: the arrows to the terminal node are injective (Lemma 5.4), and the
  image of node `i` is `R 1 ⊕ Wᵢ` (`spinDiagram_image`).
* `spinDiagramAutEquiv`: **Proposition 5.6** for groups. With `U = W ⊤` free and `2`
  invertible, `G_F(R) ≃* Stab_{O(U, B)}(W)`, the isometries of `U` preserving every `Wᵢ`.
* `spinDiagramDerEquiv`: **Proposition 5.6** for Lie algebras. `g_F(R)` corresponds to the
  `B`-skew endomorphisms of `U` preserving every `Wᵢ`.

The terminal node is `J(W ⊤, B|)`, so the statements live inside `O(W ⊤, B|)`. When `W ⊤ = ⊤`
this is `O(V, B)` (identified via `Submodule.topEquiv`).
-/

universe u w

open CategoryTheory TerminallyPointed JordanAlgebra SpinFactor

/-- The restriction of a symmetric form is symmetric. -/
instance LinearMap.BilinForm.fact_isSymm_restrict {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] (B : LinearMap.BilinForm R V) [Fact B.IsSymm] (W : Submodule R V) :
    Fact (B.restrict W).IsSymm :=
  ⟨⟨fun x y => by simpa using (Fact.out : B.IsSymm).eq x y⟩⟩

namespace JordanDiagram

noncomputable section

variable {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
variable (B : LinearMap.BilinForm R V)
variable {I : Type w} [Preorder I] [OrderTop I]

/-- The node `J(Wᵢ, B|_{Wᵢ})` of a spin-factor diagram. -/
abbrev SpinNode (W : Submodule R V) : Type u := SpinFactor R W (B.restrict W)

/-- The inclusion `J(W, B) ↪ J(W', B)` for `W ≤ W'`, a unital Jordan homomorphism. -/
def spinInclusion {W W' : Submodule R V} (h : W ≤ W') : SpinNode B W →ₙₐ[R] SpinNode B W' where
  toFun z := SpinFactor.mk (B.restrict W') (Submodule.inclusion h z.1) z.2
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem spinInclusion_apply {W W' : Submodule R V} (h : W ≤ W') (z : SpinNode B W) :
    spinInclusion B h z = SpinFactor.mk (B.restrict W') (Submodule.inclusion h z.1) z.2 := rfl

theorem spinInclusion_injective {W W' : Submodule R V} (h : W ≤ W') :
    Function.Injective (spinInclusion B h) := by
  intro z w hzw
  have h1 : (z.1 : V) = w.1 := congrArg (fun z => ((z : SpinNode B W').1 : V)) hzw
  have h2 : z.2 = w.2 := congrArg (fun z => (z : SpinNode B W').2) hzw
  exact SpinFactor.ext _ (Subtype.ext h1) h2

variable [Fact B.IsSymm]

/-- The **spin-factor diagram** of `(V, B, W)` (Definition 5.3). -/
def spinDiagram (W : I →o Submodule R V) : JordanDiagram.{u, u} R I where
  obj i := SpinNode B (W i)
  jordan _ := inferInstance
  map α := spinInclusion B (W.monotone (leOfHom α))
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

variable (W : I →o Submodule R V)

/-- **Lemma 5.4**: the terminal maps of a spin-factor diagram are injective. -/
theorem spinDiagram_ν_injective (i : I) : Function.Injective ((spinDiagram B W).ν i) :=
  spinInclusion_injective B _

omit [Fact B.IsSymm] in
variable {B} in
/-- `Wᵢ` seen inside the terminal module `W ⊤`. -/
def topPiece (i : I) : Set (W ⊤) := {u | (u : V) ∈ W i}

/-- The image of node `i` in the terminal algebra is `R 1 ⊕ Wᵢ`. -/
theorem spinDiagram_image (i : I) :
    (spinDiagram B W).image i = {z : SpinNode B (W ⊤) | z.1 ∈ topPiece W i} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact x.1.2
  · intro hz
    exact ⟨SpinFactor.mk (B.restrict (W i)) ⟨(z.1 : V), hz⟩ z.2, rfl⟩

omit [Fact B.IsSymm] in
/-- The stabilizer `Stab_{O(U, B)}(W)` of the pieces `Wᵢ`, `U = W ⊤`. -/
def orthStab : Subgroup (orthogonalGroup (B.restrict (W ⊤))) where
  carrier := {g | ∀ i u, (g : W ⊤ ≃ₗ[R] W ⊤) u ∈ topPiece W i ↔ u ∈ topPiece W i}
  one_mem' _ _ := Iff.rfl
  mul_mem' {g h} hg hh i u := by
    change (g : W ⊤ ≃ₗ[R] W ⊤) ((h : W ⊤ ≃ₗ[R] W ⊤) u) ∈ _ ↔ _
    rw [hg, hh]
  inv_mem' {g} hg i u := by
    change (g : W ⊤ ≃ₗ[R] W ⊤).symm u ∈ _ ↔ _
    rw [← hg i, LinearEquiv.apply_symm_apply]

omit [Fact B.IsSymm] in
/-- Membership in `orthStab` is `g(Wᵢ) = Wᵢ` for every `i`. -/
theorem mem_orthStab_iff_image {g : orthogonalGroup (B.restrict (W ⊤))} :
    g ∈ orthStab B W ↔ ∀ i, (g : W ⊤ ≃ₗ[R] W ⊤) '' topPiece W i = topPiece W i := by
  simp only [(g : W ⊤ ≃ₗ[R] W ⊤).bijective.image_eq_self_iff]
  rfl

variable [Invertible (2 : R)] [Module.Free R (W ⊤)]

theorem autEquivOrthogonal_mem_stabImages_iff (g : orthogonalGroup (B.restrict (W ⊤))) :
    (autEquivOrthogonal g : jordanAut R (spinDiagram B W).J) ∈ stabImages (spinDiagram B W) ↔
      g ∈ orthStab B W := by
  refine mem_stabImages.trans ?_
  simp only [jordanAut.image_eq_self_iff]
  constructor
  · intro h i u
    have := h i (SpinFactor.mk (B.restrict (W ⊤)) u 0)
    rw [spinDiagram_image] at this
    exact this
  · intro h i z
    rw [spinDiagram_image]
    exact h i z.1

/-- The stabilizer of the images, transported to the orthogonal side. -/
theorem stabImages_eq_map :
    stabImages (spinDiagram B W) = ((orthStab B W).map
      (autEquivOrthogonal (B := B.restrict (W ⊤))).toMonoidHom :
        Subgroup (jordanAut R (spinDiagram B W).J)) := by
  ext h
  constructor
  · intro hh
    obtain ⟨g, rfl⟩ := (autEquivOrthogonal (B := B.restrict (W ⊤))).surjective h
    exact ⟨g, (autEquivOrthogonal_mem_stabImages_iff B W g).1 hh, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (autEquivOrthogonal_mem_stabImages_iff B W g).2 hg

/-- **Proposition 5.6** (groups): the automorphism group of the spin-factor diagram of
`(V, B, W)` is the stabilizer in `O(W ⊤, B)` of the pieces `Wᵢ`, via `g ↦ g ⊕ id` at the
terminal node. -/
noncomputable def spinDiagramAutEquiv : (spinDiagram B W).autGroup ≃* orthStab B W :=
  (autGroupEquivStab (spinDiagram_ν_injective B W)).trans <|
    (MulEquiv.subgroupCongr (stabImages_eq_map B W)).trans
      ((autEquivOrthogonal (B := B.restrict (W ⊤))).subgroupMap (orthStab B W)).symm

/-- The terminal component of a diagram automorphism is `g ⊕ id` for the corresponding
isometry `g`. -/
theorem autEquivOrthogonal_spinDiagramAutEquiv (g : (spinDiagram B W).autGroup) :
    (autEquivOrthogonal (spinDiagramAutEquiv B W g : orthogonalGroup (B.restrict (W ⊤))) :
      jordanAut R (spinDiagram B W).J) = ev _ g :=
  congrArg Subtype.val
    (((autEquivOrthogonal (B := B.restrict (W ⊤))).subgroupMap (orthStab B W)).apply_symm_apply
      (MulEquiv.subgroupCongr (stabImages_eq_map B W)
        (autGroupEquivStab (spinDiagram_ν_injective B W) g)))

section Der

/-- `Stab_{o(U, B)}(W)`: the `B`-skew endomorphisms of `U = W ⊤` preserving every `Wᵢ`. -/
def SkewStab : Type u :=
  {X : W ⊤ →ₗ[R] W ⊤ // IsSkew (B.restrict (W ⊤)) X ∧ ∀ i, ∀ u ∈ topPiece W i, X u ∈ topPiece W i}

/-- A derivation of the terminal node preserves every image `R 1 ⊕ Wᵢ` exactly when its vector
part preserves every `Wᵢ`. -/
theorem der_preserves_iff (d : JordanDerivation R (SpinNode B (W ⊤))) :
    (∀ i, ∀ y ∈ (spinDiagram B W).image i, d y ∈ (spinDiagram B W).image i) ↔
      ∀ i, ∀ u ∈ topPiece W i, derVecPart d u ∈ topPiece W i := by
  constructor
  · intro h i u hu
    have hmem : SpinFactor.mk (B.restrict (W ⊤)) u 0 ∈ (spinDiagram B W).image i := by
      rw [spinDiagram_image]
      exact hu
    have := h i _ hmem
    rw [spinDiagram_image] at this
    exact this
  · intro h i z hz
    rw [spinDiagram_image] at hz ⊢
    have hd := der_apply_mk d z.1 z.2
    change (d (SpinFactor.mk (B.restrict (W ⊤)) z.1 z.2)).1 ∈ topPiece W i
    rw [hd]
    exact h i z.1 hz

/-- The skew map at the terminal node of a compatible family of derivations. -/
def derToSkew (D : (spinDiagram B W).derAlgebra) : SkewStab B W :=
  ⟨derVecPart (evDer _ D), derVecPart_isSkew _,
    (der_preserves_iff B W _).1 ((range_evDer (spinDiagram_ν_injective B W)).subset ⟨D, rfl⟩)⟩

/-- **Proposition 5.6** (Lie algebras): compatible derivations of the spin-factor diagram of
`(V, B, W)` are the `B`-skew endomorphisms `X` of `W ⊤` with `X(Wᵢ) ⊆ Wᵢ`, via `X ↦ X ⊕ 0` at
the terminal node. -/
noncomputable def spinDiagramDerEquiv : (spinDiagram B W).derAlgebra ≃ SkewStab B W :=
  Equiv.ofBijective (derToSkew B W) ⟨by
    intro D E hDE
    have hX : derVecPart (evDer _ D) = derVecPart (evDer _ E) := congrArg Subtype.val hDE
    apply evDer_injective (spinDiagram_ν_injective B W)
    refine JordanDerivation.ext fun z => ?_
    have hD := der_apply_mk (evDer _ D) z.1 z.2
    have hE := der_apply_mk (evDer _ E) z.1 z.2
    exact hD.trans ((congrArg
      (fun X : W ⊤ →ₗ[R] W ⊤ => SpinFactor.mk (B.restrict (W ⊤)) (X z.1) 0) hX).trans hE.symm), by
    rintro ⟨X, hX, hpres⟩
    refine ⟨ofPreserving (spinDiagram_ν_injective B W) (derOfSkew X hX)
      ((der_preserves_iff B W (derOfSkew X hX)).2 hpres), ?_⟩
    apply Subtype.ext
    exact congrArg (derVecPart (B := B.restrict (W ⊤)))
      (evDer_ofPreserving (spinDiagram_ν_injective B W) (derOfSkew X hX) _)⟩

end Der

section Iso

variable {B} {V' : Type u} [AddCommGroup V'] [Module R V'] {B' : LinearMap.BilinForm R V'}
  [Fact B'.IsSymm] (W' : I →o Submodule R V') [Module.Free R (W' ⊤)]

/-- The isometries `(W ⊤, B) ≃ (W' ⊤, B')` carrying every `Wᵢ` onto `W'ᵢ`. -/
def ConfigIsometry : Type u :=
  {g : Isometry (B.restrict (W ⊤)) (B'.restrict (W' ⊤)) //
    ∀ i u, g.1 u ∈ topPiece W' i ↔ u ∈ topPiece W i}

omit [Invertible (2 : R)] [Module.Free R (W ⊤)] [Module.Free R (W' ⊤)] in
theorem configIsometry_iff (g : Isometry (B.restrict (W ⊤)) (B'.restrict (W' ⊤))) :
    (∀ i u, g.1 u ∈ topPiece W' i ↔ u ∈ topPiece W i) ↔
      ∀ i, (equivOfIsometry g : (spinDiagram B W).J ≃ⱼ[R] (spinDiagram B' W').J) ''
        (spinDiagram B W).image i = (spinDiagram B' W').image i := by
  constructor
  · intro h i
    refine (JordanEquiv.image_eq_iff _).2 fun z => ?_
    rw [spinDiagram_image, spinDiagram_image]
    exact h i z.1
  · intro h i u
    have := (JordanEquiv.image_eq_iff _).1 (h i) (SpinFactor.mk (B.restrict (W ⊤)) u 0)
    rw [spinDiagram_image, spinDiagram_image] at this
    exact this

/-- **Proposition 5.7**: isomorphisms between spin-factor diagrams of the same shape are the
isometries of the terminal modules carrying every `Wᵢ` onto `W'ᵢ`, via `g ↦ g ⊕ id` at the
terminal node. So `(V, B, W) ↦ F_{V,B,W}` is an equivalence from configurations with isometries
onto spin-factor diagrams with isomorphisms. -/
noncomputable def spinDiagramIsoEquiv :
    DiagramIso (spinDiagram B W) (spinDiagram B' W') ≃ ConfigIsometry (B := B) (B' := B') W W' :=
  (DiagramIso.terminalEquiv (spinDiagram_ν_injective B W) (spinDiagram_ν_injective B' W')).trans
    (Equiv.subtypeEquiv isometryEquiv (configIsometry_iff W W')).symm

end Iso

end

end JordanDiagram
