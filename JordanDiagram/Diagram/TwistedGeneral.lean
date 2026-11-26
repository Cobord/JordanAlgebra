module

public import JordanDiagram.Diagram.Iso

/-!
# The shape-twisted group for general shapes

Let `(I⁺, +)` be a terminally pointed small category and `F` a diagram over it.

* `ShapeAut I`: the group `Aut(I⁺, +)` of strict automorphisms of the category `I⁺` fixing the
  chosen terminal object `+`.
* `ShapeTwistedAut F`: **the shape-twisted group `G̃_F(R)`**: pairs `(u, θ)` with `u ∈ Aut(I⁺, +)`
  and Jordan isomorphisms `θᵢ : F(i) ≃ F(u i)` satisfying `θⱼ ∘ F(α) = F(u α) ∘ θᵢ`, with
  `(u, θ)(v, η) = (u v, θ_v ∘ η)`. Equalities between objects of `I⁺` are transported along
  `F(eqToHom _)` (`castEquiv`).
* `ShapeTwistedAut.range_ofAut`: **the sequence `1 → G_F(R) → G̃_F(R) → Aut(I⁺, +)` is exact**.
* `ShapeTwistedAut.terminalEquiv`: **terminal determination**: when every terminal map is
  injective, with images `Aᵢ ⊆ J`, `(u, θ) ↦ (u, θ₊)` identifies `G̃_F(R)` with the group of pairs
  `(u, h)`, `u ∈ Aut(I⁺, +)`, `h ∈ Aut(J)`, with `h(Aᵢ) = A_{u(i)}` for every `i`.
-/

@[expose] public section

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

namespace JordanDiagram

/-! ### Strict automorphisms of the shape -/

variable (I : Type w) [Category.{w'} I] [TerminallyPointed I]

/-- A strict automorphism of the category `I⁺` fixing the terminal object `+`. -/
structure ShapeAut where
  /-- The automorphism. -/
  functor : I ⥤ I
  /-- Its inverse. -/
  inv : I ⥤ I
  functor_inv : functor ⋙ inv = 𝟭 I
  inv_functor : inv ⋙ functor = 𝟭 I
  obj_top : functor.obj top = top

namespace ShapeAut

variable {I}

theorem inv_eq_of_functor_eq {a b : ShapeAut I} (h : a.functor = b.functor) : a.inv = b.inv :=
  calc a.inv = a.inv ⋙ (b.functor ⋙ b.inv) := by rw [b.functor_inv]; rfl
    _ = (a.inv ⋙ a.functor) ⋙ b.inv := by rw [h]; rfl
    _ = b.inv := by rw [a.inv_functor]; rfl

@[ext]
theorem ext {a b : ShapeAut I} (h : a.functor = b.functor) : a = b := by
  obtain ⟨f, g, _, _, _⟩ := a
  obtain ⟨f', g', _, _, _⟩ := b
  have hg := inv_eq_of_functor_eq (a := ⟨f, g, ‹_›, ‹_›, ‹_›⟩) (b := ⟨f', g', ‹_›, ‹_›, ‹_›⟩) h
  dsimp only at h hg
  subst h hg
  rfl

theorem inv_obj_top (a : ShapeAut I) : a.inv.obj top = top := by
  have := Functor.congr_obj a.functor_inv top
  rw [Functor.comp_obj, a.obj_top] at this
  exact this

instance : Group (ShapeAut I) where
  mul a b := ⟨b.functor ⋙ a.functor, a.inv ⋙ b.inv,
    by
      change b.functor ⋙ (a.functor ⋙ a.inv) ⋙ b.inv = _
      rw [a.functor_inv]
      exact b.functor_inv,
    by
      change a.inv ⋙ (b.inv ⋙ b.functor) ⋙ a.functor = _
      rw [b.inv_functor]
      exact a.inv_functor,
    by
      change a.functor.obj (b.functor.obj top) = top
      rw [b.obj_top, a.obj_top]⟩
  one := ⟨𝟭 I, 𝟭 I, rfl, rfl, rfl⟩
  inv a := ⟨a.inv, a.functor, a.inv_functor, a.functor_inv, a.inv_obj_top⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel a := ShapeAut.ext a.functor_inv

theorem mul_functor (a b : ShapeAut I) : (a * b).functor = b.functor ⋙ a.functor := rfl

theorem one_functor : (1 : ShapeAut I).functor = 𝟭 I := rfl

theorem inv_functor' (a : ShapeAut I) : a⁻¹.functor = a.inv := rfl

end ShapeAut

/-! ### The shape-twisted group -/

variable {R : Type u} [CommRing R] {I} (F : JordanDiagram.{u, v} R I)

omit [TerminallyPointed I] in
/-- Transport between the nodes at equal objects, `F(eqToHom h)`. -/
def castEquiv' {i j : I} (h : i = j) : F.obj i ≃ⱼ[R] F.obj j :=
  ⟨{ toFun := F.map (eqToHom h)
     invFun := F.map (eqToHom h.symm)
     map_add' := map_add _
     map_smul' := map_smul _
     left_inv := fun x => by rw [← F.map_comp, eqToHom_trans, eqToHom_refl, F.map_id]
     right_inv := fun x => by rw [← F.map_comp, eqToHom_trans, eqToHom_refl, F.map_id] },
    fun x y => map_mul (F.map (eqToHom h)) x y⟩

omit [TerminallyPointed I] in
theorem castEquiv'_apply {i j : I} (h : i = j) (x : F.obj i) :
    F.castEquiv' h x = F.map (eqToHom h) x := rfl

omit [TerminallyPointed I] in
/-- A loop of object identities acts trivially. -/
theorem map_eqToHom_loop {k l : I} (p : k = l) (q : l = k) (y : F.obj k) :
    F.map (eqToHom p ≫ eqToHom q) y = y := by
  subst p
  rw [eqToHom_trans, eqToHom_refl, F.map_id]

/-- **Shape-twisted automorphisms**: a shape automorphism `u` with Jordan isomorphisms
`θᵢ : F(i) ≃ F(u i)` satisfying `θⱼ ∘ F(α) = F(u α) ∘ θᵢ`. -/
structure ShapeTwistedAut where
  /-- The automorphism of the shape. -/
  shape : ShapeAut I
  /-- The component at node `i`. -/
  app : ∀ i, F.obj i ≃ⱼ[R] F.obj (shape.functor.obj i)
  naturality : ∀ {i j : I} (α : i ⟶ j) (x : F.obj i),
    app j (F.map α x) = F.map (shape.functor.map α) (app i x)

namespace ShapeTwistedAut

variable {F}

/-- Twisted automorphisms are equal when their shapes agree and their components agree after
transport. -/
theorem ext' {a b : ShapeTwistedAut F} (hs : a.shape = b.shape)
    (h : ∀ i x (e : a.shape.functor.obj i = b.shape.functor.obj i),
      F.map (eqToHom e) (a.app i x) = b.app i x) : a = b := by
  obtain ⟨sa, appa, na⟩ := a
  obtain ⟨sb, appb, nb⟩ := b
  dsimp only at hs
  subst hs
  congr
  funext i
  exact JordanEquiv.ext fun x => by
    have := h i x rfl
    rwa [eqToHom_refl, F.map_id] at this

instance : Mul (ShapeTwistedAut F) where
  mul a b := ⟨a.shape * b.shape, fun i => (b.app i).trans (a.app (b.shape.functor.obj i)),
    fun α x => (congrArg (a.app _) (b.naturality α x)).trans (a.naturality _ _)⟩

instance : One (ShapeTwistedAut F) where
  one := ⟨1, fun _ => JordanEquiv.refl R _, fun _ _ => rfl⟩

/-- The object identity `u (u⁻¹ i) = i`. -/
theorem functor_inv_obj (u : ShapeAut I) (i : I) : u.functor.obj (u.inv.obj i) = i :=
  Functor.congr_obj u.inv_functor i

/-- The object identity `u⁻¹ (u i) = i`. -/
theorem inv_functor_obj (u : ShapeAut I) (i : I) : u.inv.obj (u.functor.obj i) = i :=
  Functor.congr_obj u.functor_inv i

/-- `u (u⁻¹ α)` is `α` up to the object identities. -/
theorem functor_map_inv_map (u : ShapeAut I) {i j : I} (α : i ⟶ j) :
    eqToHom (functor_inv_obj u i).symm ≫ u.functor.map (u.inv.map α) =
      α ≫ eqToHom (functor_inv_obj u j).symm := by
  have := Functor.congr_hom u.inv_functor α
  rw [Functor.comp_map] at this
  rw [this]
  simp

instance : Inv (ShapeTwistedAut F) where
  inv a := ⟨a.shape⁻¹, fun i =>
    (F.castEquiv' (functor_inv_obj a.shape i).symm).trans (a.app (a.shape.inv.obj i)).symm,
    fun {i j} α x => by
      apply (a.app (a.shape.inv.obj j)).injective
      change a.app _ ((a.app _).symm (F.castEquiv' _ (F.map α x))) =
        a.app _ (F.map (a.shape.inv.map α) ((a.app _).symm (F.castEquiv' _ x)))
      rw [JordanEquiv.apply_symm_apply, a.naturality, JordanEquiv.apply_symm_apply,
        castEquiv'_apply, castEquiv'_apply, ← F.map_comp, ← F.map_comp, functor_map_inv_map]⟩

theorem mul_shape (a b : ShapeTwistedAut F) : (a * b).shape = a.shape * b.shape := rfl

theorem mul_app (a b : ShapeTwistedAut F) (i : I) (x : F.obj i) :
    (a * b).app i x = a.app (b.shape.functor.obj i) (b.app i x) := rfl

theorem one_shape : (1 : ShapeTwistedAut F).shape = 1 := rfl

theorem inv_shape (a : ShapeTwistedAut F) : a⁻¹.shape = a.shape⁻¹ := rfl

/-- **The shape-twisted group** `G̃_F(R)`. -/
instance instGroup : Group (ShapeTwistedAut F) where
  mul_assoc _ _ _ := ext' rfl fun _ _ _ => by rw [eqToHom_refl, F.map_id]; rfl
  one_mul _ := ext' rfl fun _ _ _ => by rw [eqToHom_refl, F.map_id]; rfl
  mul_one _ := ext' rfl fun _ _ _ => by rw [eqToHom_refl, F.map_id]; rfl
  inv_mul_cancel a := ext' (inv_mul_cancel a.shape) fun i x e => by
    apply (a.app i).injective
    have hn := a.naturality (eqToHom (inv_functor_obj a.shape i))
      ((a.app (a.shape.inv.obj (a.shape.functor.obj i))).symm
        (F.castEquiv' (functor_inv_obj a.shape (a.shape.functor.obj i)).symm (a.app i x)))
    rw [JordanEquiv.apply_symm_apply, castEquiv'_apply, ← F.map_comp, eqToHom_map,
      eqToHom_trans, eqToHom_refl, F.map_id] at hn
    exact hn

variable (F) in
/-- The shape automorphism, `G̃_F(R) → Aut(I⁺, +)`. -/
def shapeHom : ShapeTwistedAut F →* ShapeAut I where
  toFun := shape
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F) in
/-- A diagram automorphism as a twisted automorphism over the identity. -/
def ofAut : F.autGroup →* ShapeTwistedAut F where
  toFun g := ⟨1, fun i => JordanEquiv.ofAut (g.1 i), fun α x => autGroup_naturality g α x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ofAut_injective : Function.Injective (ofAut F) := by
  intro g h hgh
  have happ := eq_of_heq (ShapeTwistedAut.mk.inj hgh).2
  apply Subtype.ext
  funext i
  apply jordanAut.ext
  intro x
  exact congrArg (fun f : ∀ i, F.obj i ≃ⱼ[R] F.obj i => f i x) happ

/-- **Exactness of `1 → G_F(R) → G̃_F(R) → Aut(I⁺, +)`**. -/
theorem range_ofAut : (ofAut F).range = (shapeHom F).ker := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    rfl
  · intro ha
    have hs : a.shape = 1 := ha
    have hi : ∀ i, a.shape.functor.obj i = i := fun i => by rw [hs]; rfl
    refine ⟨⟨fun i => ((a.app i).trans (F.castEquiv' (hi i))).toAut, fun {i j} α x => ?_⟩, ?_⟩
    · change F.castEquiv' (hi j) (a.app j (F.map α x)) =
        F.map α (F.castEquiv' (hi i) (a.app i x))
      rw [a.naturality, castEquiv'_apply, castEquiv'_apply, ← F.map_comp, ← F.map_comp]
      congr 1
      have := Functor.congr_hom (congrArg ShapeAut.functor hs) α
      rw [this]
      simp
      rfl
    · refine ext' hs.symm fun i x e => ?_
      change F.map _ (F.castEquiv' (hi i) (a.app i x)) = a.app i x
      rw [castEquiv'_apply]
      exact (F.map_comp _ _ _).symm.trans (map_eqToHom_loop F _ _ _)

/-- The kernel of `G̃_F(R) → Aut(I⁺, +)` is `G_F(R)`. -/
noncomputable def autGroupEquivKer : F.autGroup ≃* (shapeHom F).ker :=
  (MonoidHom.ofInjective ofAut_injective).trans (MulEquiv.subgroupCongr range_ofAut)

/-! #### Terminal determination -/

omit [TerminallyPointed I] in
theorem map_eqToHom_map_eqToHom {k l m : I} (p : k = l) (q : l = m) (y : F.obj k) :
    F.map (eqToHom q) (F.map (eqToHom p) y) = F.map (eqToHom (p.trans q)) y := by
  rw [← F.map_comp, eqToHom_trans]

/-- The terminal component `θ₊ : J → J`, after transport along `u(+) = +`. -/
def topAut (a : ShapeTwistedAut F) : jordanAut R F.TerminalJordanAlgebra :=
  ((a.app top).trans (F.castEquiv' a.shape.obj_top)).toAut

theorem topAut_apply (a : ShapeTwistedAut F) (y : F.TerminalJordanAlgebra) :
    topAut a y = F.map (eqToHom a.shape.obj_top) (a.app top y) := rfl

/-- The terminal relation `θ₊ ∘ νᵢ = ν_{u(i)} ∘ θᵢ`. -/
theorem topAut_ν (a : ShapeTwistedAut F) (i : I) (x : F.obj i) :
    topAut a (F.ν i x) = F.ν (a.shape.functor.obj i) (a.app i x) := by
  rw [topAut_apply]
  change F.map _ (a.app top (F.map (toTop i) x)) = F.map (toTop _) _
  rw [a.naturality, ← F.map_comp]
  exact congrArg (fun f => F.map f (a.app i x)) (hom_ext _ _)

theorem topAut_mul (a b : ShapeTwistedAut F) : topAut (a * b) = topAut a * topAut b := by
  refine jordanAut.ext fun y => ?_
  rw [jordanAut.mul_apply, topAut_apply, topAut_apply, topAut_apply, mul_app]
  have hn := a.naturality (eqToHom b.shape.obj_top) (b.app top y)
  rw [eqToHom_map] at hn
  rw [hn, map_eqToHom_map_eqToHom]

theorem topAut_one : topAut (1 : ShapeTwistedAut F) = 1 :=
  jordanAut.ext fun y => by
    rw [topAut_apply]
    exact (congrArg (fun f => F.map f y) (eqToHom_refl _ _)).trans (F.map_id _ y)

variable (F) in
/-- The pairs `(u, h)` with `u ∈ Aut(I⁺, +)`, `h ∈ Aut(J)` and `h(Aᵢ) = A_{u(i)}` for every `i`. -/
def terminalPairs : Subgroup (ShapeAut I × jordanAut R F.TerminalJordanAlgebra) where
  carrier := {p | ∀ i, p.2 '' F.image i = F.image (p.1.functor.obj i)}
  one_mem' i := by
    change (fun y => (1 : jordanAut R F.TerminalJordanAlgebra) y) '' F.image i = F.image i
    simp
  mul_mem' {p q} hp hq i := by
    change (p.2 * q.2) '' F.image i = F.image (p.1.functor.obj (q.1.functor.obj i))
    rw [← hp, ← hq, Set.image_image]
    rfl
  inv_mem' {p} hp i := by
    change ⇑((p.2)⁻¹ : jordanAut R F.TerminalJordanAlgebra) '' F.image i = F.image (p.1.inv.obj i)
    have := hp (p.1.inv.obj i)
    rw [functor_inv_obj] at this
    rw [← this, Set.image_image]
    simp

theorem mem_terminalPairs {p : ShapeAut I × jordanAut R F.TerminalJordanAlgebra} :
    p ∈ terminalPairs F ↔ ∀ i, p.2 '' F.image i = F.image (p.1.functor.obj i) := Iff.rfl

theorem topAut_image (a : ShapeTwistedAut F) (i : I) :
    topAut a '' F.image i = F.image (a.shape.functor.obj i) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨a.app i x, (topAut_ν a i x).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨F.ν i ((a.app i).symm z), ⟨_, rfl⟩, ?_⟩
    rw [topAut_ν, JordanEquiv.apply_symm_apply]

variable (F) in
/-- `(u, θ) ↦ (u, θ₊)`, a homomorphism into the group of pairs. -/
def toTerminal : ShapeTwistedAut F →* terminalPairs F where
  toFun a := ⟨(a.shape, topAut a), topAut_image a⟩
  map_one' := Subtype.ext (Prod.ext rfl topAut_one)
  map_mul' a b := Subtype.ext (Prod.ext rfl (topAut_mul a b))

variable (hν : ∀ i, Function.Injective (F.ν i))
include hν

theorem toTerminal_injective : Function.Injective (toTerminal F) := by
  intro a b hab
  have h1 : a.shape = b.shape := congrArg (fun p : terminalPairs F => p.1.1) hab
  have h2 : topAut a = topAut b := congrArg (fun p : terminalPairs F => p.1.2) hab
  refine ext' h1 fun i x e => hν (b.shape.functor.obj i) ?_
  rw [F.ν_map, ← topAut_ν, ← topAut_ν, h2]

omit hν in
theorem terminalPairs_image (p : terminalPairs F) (i : I) :
    (JordanEquiv.ofAut p.1.2) '' Set.range (F.ν i) = Set.range (F.ν (p.1.1.functor.obj i)) :=
  mem_terminalPairs.1 p.2 i

/-- The twisted automorphism over `u` with terminal component `h`, for `h(Aᵢ) = A_{u(i)}`. -/
noncomputable def ofTerminal (p : terminalPairs F) : ShapeTwistedAut F :=
  ⟨p.1.1, fun i => JordanEquiv.lift (hν i) (hν (p.1.1.functor.obj i)) (JordanEquiv.ofAut p.1.2)
      (terminalPairs_image p i),
    fun {i j} α x => hν (p.1.1.functor.obj j) (by
      rw [JordanEquiv.lift_spec, F.ν_map, F.ν_map, JordanEquiv.lift_spec])⟩

theorem toTerminal_surjective : Function.Surjective (toTerminal F) := by
  intro p
  refine ⟨ofTerminal hν p, Subtype.ext (Prod.ext rfl (jordanAut.ext fun y => ?_))⟩
  change topAut (ofTerminal hν p) y = p.1.2 y
  conv_lhs => rw [← F.ν_top y]
  rw [topAut_ν]
  have := JordanEquiv.lift_spec (hν top) (hν (p.1.1.functor.obj top)) (JordanEquiv.ofAut p.1.2)
    (terminalPairs_image p top) y
  rw [F.ν_top] at this
  exact this

/-- **Terminal determination for twisted automorphisms**: when every terminal map is injective,
`(u, θ) ↦ (u, θ₊)` identifies `G̃_F(R)` with the group of pairs `(u, h)`, `h ∈ Aut(J)`, with
`h(Aᵢ) = A_{u(i)}` for every `i`. -/
noncomputable def terminalEquiv : ShapeTwistedAut F ≃* terminalPairs F :=
  MulEquiv.ofBijective (toTerminal F) ⟨toTerminal_injective hν, toTerminal_surjective hν⟩

omit hν in
theorem toTerminal_apply (a : ShapeTwistedAut F) :
    (toTerminal F a : ShapeAut I × jordanAut R F.TerminalJordanAlgebra) = (a.shape, topAut a) := rfl

end ShapeTwistedAut

end JordanDiagram
