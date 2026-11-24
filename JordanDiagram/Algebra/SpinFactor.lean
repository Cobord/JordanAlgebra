module

public import JordanDiagram.Algebra.Equiv
public import Jordan.SpinFactor
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Isomorphisms, automorphisms and derivations of spin factors (Lemma 5.5)

For free `R`-modules `V`, `V'` with arbitrary symmetric bilinear forms `B`, `B'` (possibly
degenerate), over a commutative ring with `2` invertible:

* `Isometry B B'`, the isometries `(V, B) ≃ (V', B')`, and `isometryEquiv`: every Jordan
  isomorphism `J(V, B) ≃ⱼ J(V', B')` is `g ⊕ id` for a unique isometry `g` (Lemma 5.5);
* `orthogonalGroup B`, the group `O(V, B)(R)` (Definition 5.2), and `autEquivOrthogonal`:
  `O(V, B)(R) ≃* Aut_{Jord_R} J(V, B)`, `g ↦ g ⊕ id`, the case `V = V'`;
* `IsSkew B X` (`X ∈ o(V, B)(R)`), and `derEquivSkew`: derivations of `J(V, B)` are exactly the
  maps `X ⊕ 0` with `X` skew for `B` (Lemma 5.5).

The proof follows the paper's: an isomorphism `e` fixes the unit. For a basis vector `v`, write
`e(v) = (u, t)`; applying `e⁻¹` to the quadratic relation `x² = T(x) x - N(x) 1` gives `2 t v = 0`,
so `e(V) ⊆ V'`. Multiplicativity on `v * w = B(v, w) 1` then gives the isometry property directly,
with no polarization.

The spin factor's `JordanAlgebra` structure is a definition depending on symmetry of `B`
(`SpinFactor.jordanAlgebra`); here it is made a scoped instance under `[Fact B.IsSymm]`.
-/

@[expose] public section

open JordanAlgebra

noncomputable section

namespace SpinFactor

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (B : LinearMap.BilinForm R V)

/-- The spin factor of a symmetric form, as an instance under `Fact B.IsSymm`. -/
noncomputable scoped instance instJordanAlgebraOfFact [Fact B.IsSymm] :
    JordanAlgebra R (SpinFactor R V B) :=
  jordanAlgebra B Fact.out

/-- The orthogonal group `O(V, B)(R)` (Definition 5.2). -/
def orthogonalGroup : Subgroup (V ≃ₗ[R] V) where
  carrier := {g | ∀ v w, B (g v) (g w) = B v w}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh v w := by
    change B (g (h v)) (g (h w)) = B v w
    rw [hg, hh]
  inv_mem' {g} hg v w := by
    change B (g.symm v) (g.symm w) = B v w
    conv_rhs => rw [← g.apply_symm_apply v, ← g.apply_symm_apply w]
    exact (hg _ _).symm

/-- `X ∈ o(V, B)(R)`: `B (X v) w + B v (X w) = 0` (Definition 5.2). -/
def IsSkew (X : V →ₗ[R] V) : Prop := ∀ v w, B (X v) w + B v (X w) = 0

@[simp] theorem mk_mul_mk (x y : V) (a b : R) :
    mk B x a * mk B y b = mk B (a • y + b • x) (B x y + a * b) := rfl

theorem mk_zero_mul_mk_zero (v w : V) : mk B v 0 * mk B w 0 = mk B 0 (B v w) := by
  ext <;> simp

theorem eq_mk (z : SpinFactor R V B) : z = mk B z.1 z.2 := rfl

theorem mk_add (x y : V) (a b : R) : mk B (x + y) (a + b) = mk B x a + mk B y b := rfl

theorem mk_zero_eq_smul_one (r : R) : mk B 0 r = r • (1 : SpinFactor R V B) := by
  ext <;> simp

theorem mk_eq_mk_zero_add (v : V) (r : R) : mk B v r = mk B v 0 + r • (1 : SpinFactor R V B) := by
  ext <;> simp

/-- The quadratic relation `x² - T(x) x + N(x) 1 = 0`, `T(u, t) = 2t`, `N(u, t) = t² - B(u, u)`. -/
theorem quad (u : V) (t : R) :
    mk B u t * mk B u t + (t * t - B u u) • (1 : SpinFactor R V B) = (2 * t) • mk B u t := by
  ext
  · simp only [mk_mul_mk, add_fst, mk_fst, smul_fst, one_fst, smul_zero, add_zero]
    rw [two_mul, add_smul]
  · simp only [mk_mul_mk, add_snd, mk_snd, smul_snd, one_snd, smul_eq_mul, mul_one]
    ring

section Iso

variable {B} {V' : Type*} [AddCommGroup V'] [Module R V'] {B' : LinearMap.BilinForm R V'}

/-- Isometries `(V, B) ≃ (V', B')`. -/
def Isometry (B : LinearMap.BilinForm R V) (B' : LinearMap.BilinForm R V') : Type _ :=
  {g : V ≃ₗ[R] V' // ∀ v w, B' (g v) (g w) = B v w}

variable [Fact B.IsSymm] [Fact B'.IsSymm]

/-- The Jordan isomorphism `g ⊕ id : J(V, B) ≃ⱼ J(V', B')` attached to an isometry `g`. -/
def equivOfIsometry (g : Isometry B B') : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B' :=
  ⟨{ toFun := fun z => mk B' (g.1 z.1) z.2
     invFun := fun z => mk B (g.1.symm z.1) z.2
     map_add' := fun z w => by ext <;> simp
     map_smul' := fun r z => by ext <;> simp
     left_inv := fun z => by ext <;> simp
     right_inv := fun z => by ext <;> simp },
   fun z w => by
     ext
     · simp
     · simp [g.2 z.1 w.1]⟩

@[simp]
theorem equivOfIsometry_apply (g : Isometry B B') (z : SpinFactor R V B) :
    equivOfIsometry g z = mk B' (g.1 z.1) z.2 := rfl

/-- Jordan isomorphisms of spin factors preserve the unit. -/
theorem jordanEquiv_one (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') : e 1 = 1 := by
  have h : e 1 * e (e.symm 1) = e (e.symm 1) := by rw [← e.map_mul, one_mul]
  rw [JordanEquiv.apply_symm_apply, mul_one] at h
  exact h

variable [Invertible (2 : R)]

/-- The scalar part of `e (v, 0)` vanishes when `r • v = 0 → r = 0`. -/
theorem snd_apply_mk_zero_of_torsionFree (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v : V)
    (hv : ∀ r : R, r • v = 0 → r = 0) : (e (mk B v 0)).2 = 0 := by
  obtain ⟨u, t, hx⟩ : ∃ u t, e (mk B v 0) = mk B' u t := ⟨_, _, rfl⟩
  rw [hx]
  change t = 0
  -- apply `e⁻¹` to the quadratic relation for `e (v, 0) = (u, t)`
  have hq := congrArg (fun z => e.symm z) (quad B' u t)
  have hl : e.symm (mk B' u t * mk B' u t + (t * t - B' u u) • (1 : SpinFactor R V' B')) =
      mk B 0 (B v v) + (t * t - B' u u) • (1 : SpinFactor R V B) := by
    change e.symm.toLinearEquiv _ = _
    rw [map_add, map_smul]
    change e.symm (mk B' u t * mk B' u t) + _ • e.symm 1 = _
    rw [JordanEquiv.map_mul, ← hx, JordanEquiv.symm_apply_apply, jordanEquiv_one e.symm,
      mk_zero_mul_mk_zero]
  have hr : e.symm ((2 * t) • mk B' u t) = (2 * t) • mk B v 0 := by
    change e.symm.toLinearEquiv _ = _
    rw [map_smul]
    change _ • e.symm (mk B' u t) = _
    rw [← hx, JordanEquiv.symm_apply_apply]
  have h := hl.symm.trans (hq.trans hr)
  have h1 := congrArg Prod.fst h
  simp only [add_fst, mk_fst, smul_fst, one_fst, smul_zero, add_zero] at h1
  have h3 := hv _ h1.symm
  calc t = ⅟(2 : R) * (2 * t) := by rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [h3, mul_zero]

/-- The vector part of a Jordan isomorphism, as a linear map `V → V'`. -/
def vecPart (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') : V →ₗ[R] V' :=
  (fstLinear B') ∘ₗ (e.toLinearEquiv.toLinearMap) ∘ₗ (LinearMap.inl R V R)

omit [Invertible (2 : R)] in
theorem vecPart_apply (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v : V) :
    vecPart e v = (e (mk B v 0)).1 := rfl

variable [Module.Free R V]

/-- Every Jordan isomorphism `J(V, B) ≃ⱼ J(V', B')` maps `V` into `V'`. -/
theorem snd_apply_mk_zero (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v : V) :
    (e (mk B v 0)).2 = 0 := by
  let b := Module.Free.chooseBasis R V
  let f : V →ₗ[R] R := (sndLinear B') ∘ₗ (e.toLinearEquiv.toLinearMap) ∘ₗ (LinearMap.inl R V R)
  have hf : f = 0 := b.ext fun i => by
    refine snd_apply_mk_zero_of_torsionFree e (b i) fun r hr => ?_
    have := congrArg (fun w => b.repr w i) hr
    simpa using this
  exact LinearMap.congr_fun hf v

theorem apply_mk_zero (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v : V) :
    e (mk B v 0) = mk B' (vecPart e v) 0 := by
  ext
  · rfl
  · exact snd_apply_mk_zero e v

theorem apply_mk (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v : V) (r : R) :
    e (mk B v r) = mk B' (vecPart e v) r := by
  rw [mk_eq_mk_zero_add]
  change e.toLinearEquiv _ = _
  rw [map_add, map_smul]
  change e (mk B v 0) + r • e 1 = _
  rw [jordanEquiv_one, apply_mk_zero]
  ext <;> simp

theorem vecPart_symm_vecPart (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v : V) :
    vecPart e.symm (vecPart e v) = v := by
  rw [vecPart_apply, ← apply_mk_zero, JordanEquiv.symm_apply_apply]
  rfl

theorem vecPart_isometry (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') (v w : V) :
    B' (vecPart e v) (vecPart e w) = B v w := by
  have h := e.map_mul (mk B v 0) (mk B w 0)
  rw [mk_zero_mul_mk_zero, apply_mk, apply_mk_zero e v, apply_mk_zero e w,
    mk_zero_mul_mk_zero] at h
  have := congrArg Prod.snd h
  simpa using this.symm

variable [Module.Free R V']

/-- The isometry underlying a Jordan isomorphism. -/
def isometryOfEquiv (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') : Isometry B B' :=
  ⟨LinearEquiv.ofLinearMap (vecPart e) (vecPart e.symm)
    (LinearMap.ext fun v => by
      have := vecPart_symm_vecPart e.symm v
      rwa [JordanEquiv.symm_symm] at this)
    (LinearMap.ext fun v => vecPart_symm_vecPart e v),
   vecPart_isometry e⟩

theorem equivOfIsometry_isometryOfEquiv (e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') :
    equivOfIsometry (isometryOfEquiv e) = e := by
  refine JordanEquiv.ext fun z => ?_
  obtain ⟨v, r⟩ := z
  exact (apply_mk e v r).symm

/-- **Lemma 5.5** (isomorphisms): for `V`, `V'` free and `B`, `B'` any symmetric bilinear forms,
with `2` invertible, every Jordan isomorphism `J(V, B) ≃ⱼ J(V', B')` is `g ⊕ id` for a unique
isometry `g : (V, B) ≃ (V', B')`. -/
def isometryEquiv : Isometry B B' ≃ (SpinFactor R V B ≃ⱼ[R] SpinFactor R V' B') where
  toFun := equivOfIsometry
  invFun := isometryOfEquiv
  left_inv _ := Subtype.ext (LinearEquiv.ext fun _ => rfl)
  right_inv := equivOfIsometry_isometryOfEquiv

end Iso

section Aut

variable {B} [Fact B.IsSymm]

/-- The Jordan automorphism `g ⊕ id` of `J(V, B)` attached to an isometry `g`. -/
def autOfOrthogonal (g : orthogonalGroup B) : jordanAut R (SpinFactor R V B) :=
  (equivOfIsometry (B' := B) ⟨g.1, g.2⟩).toAut

@[simp]
theorem autOfOrthogonal_apply (g : orthogonalGroup B) (z : SpinFactor R V B) :
    autOfOrthogonal g z = mk B ((g : V ≃ₗ[R] V) z.1) z.2 := rfl

/-- `g ↦ g ⊕ id` as a group homomorphism `O(V, B)(R) → Aut J(V, B)`. -/
def autOfOrthogonalHom : orthogonalGroup B →* jordanAut R (SpinFactor R V B) where
  toFun := autOfOrthogonal
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

theorem autOfOrthogonalHom_injective :
    Function.Injective (autOfOrthogonalHom (R := R) (V := V) (B := B)) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun a : jordanAut R (SpinFactor R V B) => (a (mk B v 0)).1) hgh
  simpa [autOfOrthogonalHom] using this

/-- Jordan automorphisms fix the unit. -/
theorem jordanAut_one (a : jordanAut R (SpinFactor R V B)) : a 1 = 1 :=
  jordanEquiv_one (JordanEquiv.ofAut a)

variable [Invertible (2 : R)] [Module.Free R V]

/-- The isometry underlying a Jordan automorphism. -/
def orthogonalOfAut (a : jordanAut R (SpinFactor R V B)) : orthogonalGroup B :=
  ⟨(isometryOfEquiv (JordanEquiv.ofAut a)).1, (isometryOfEquiv (JordanEquiv.ofAut a)).2⟩

theorem autOfOrthogonal_orthogonalOfAut (a : jordanAut R (SpinFactor R V B)) :
    autOfOrthogonal (orthogonalOfAut a) = a := by
  refine jordanAut.ext fun z => ?_
  exact congrArg (fun e : SpinFactor R V B ≃ⱼ[R] SpinFactor R V B => e z)
    (equivOfIsometry_isometryOfEquiv (JordanEquiv.ofAut a))

/-- **Lemma 5.5** (automorphisms): for `V` free and `B` any symmetric bilinear form, with `2`
invertible, `g ↦ g ⊕ id` is an isomorphism `O(V, B)(R) ≃* Aut_{Jord_R} J(V, B)`. -/
noncomputable def autEquivOrthogonal : orthogonalGroup B ≃* jordanAut R (SpinFactor R V B) :=
  MulEquiv.ofBijective autOfOrthogonalHom
    ⟨autOfOrthogonalHom_injective, fun a => ⟨orthogonalOfAut a, autOfOrthogonal_orthogonalOfAut a⟩⟩

@[simp]
theorem autEquivOrthogonal_apply (g : orthogonalGroup B) (z : SpinFactor R V B) :
    autEquivOrthogonal g z = mk B ((g : V ≃ₗ[R] V) z.1) z.2 := rfl

end Aut

section Der

variable {B} [Fact B.IsSymm]

/-- The derivation `X ⊕ 0` of `J(V, B)` attached to a skew map `X`. -/
def derOfSkew (X : V →ₗ[R] V) (hX : IsSkew B X) : JordanDerivation R (SpinFactor R V B) where
  toFun z := mk B (X z.1) 0
  map_add' z w := by ext <;> simp
  map_smul' r z := by ext <;> simp
  leibniz' z w := by
    ext
    · simp [add_comm]
    · simp [hX z.1 w.1, add_comm]

@[simp]
theorem derOfSkew_apply (X : V →ₗ[R] V) (hX : IsSkew B X) (z : SpinFactor R V B) :
    derOfSkew X hX z = mk B (X z.1) 0 := rfl

variable [Invertible (2 : R)] [Module.Free R V]

theorem der_snd_mk_zero (d : JordanDerivation R (SpinFactor R V B)) (v : V) :
    (d (mk B v 0)).2 = 0 := by
  let b := Module.Free.chooseBasis R V
  let f : V →ₗ[R] R := (sndLinear B) ∘ₗ (d : SpinFactor R V B →ₗ[R] _) ∘ₗ (LinearMap.inl R V R)
  suffices hf : f = 0 from LinearMap.congr_fun hf v
  refine b.ext fun i => ?_
  -- `d(e * e) = d(B(e,e) 1) = 0`, while `d(e * e) = 2 e * d e = (2 λ(e) e, 2 B(e, X e))`
  have h := d.leibniz (mk B (b i) 0) (mk B (b i) 0)
  rw [mk_zero_mul_mk_zero, mk_zero_eq_smul_one, d.map_smul, d.map_one_eq_zero, smul_zero] at h
  have h1 := congrArg (fun z => b.repr z.1 i) h
  simp at h1
  have h2 : (2 : R) * (d (mk B (b i) 0)).2 = 0 := by
    rw [two_mul]
    simpa [mk] using h1.symm
  change (d (mk B (b i) 0)).2 = 0
  calc (d (mk B (b i) 0)).2 = ⅟(2 : R) * (2 * (d (mk B (b i) 0)).2) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [h2, mul_zero]

theorem der_apply_mk (d : JordanDerivation R (SpinFactor R V B)) (v : V) (r : R) :
    d (mk B v r) = mk B (d (mk B v 0)).1 0 := by
  rw [mk_eq_mk_zero_add, d.map_add, d.map_smul, d.map_one_eq_zero, smul_zero, add_zero]
  ext
  · rfl
  · exact der_snd_mk_zero d v

/-- The vector part of a derivation, as a linear map `V → V`. -/
def derVecPart (d : JordanDerivation R (SpinFactor R V B)) : V →ₗ[R] V :=
  (fstLinear B) ∘ₗ (d : SpinFactor R V B →ₗ[R] _) ∘ₗ (LinearMap.inl R V R)

omit [Invertible (2 : R)] [Module.Free R V] in
theorem derVecPart_apply (d : JordanDerivation R (SpinFactor R V B)) (v : V) :
    derVecPart d v = (d (mk B v 0)).1 := rfl

theorem derVecPart_isSkew (d : JordanDerivation R (SpinFactor R V B)) :
    IsSkew B (derVecPart d) := by
  intro v w
  have h := d.leibniz (mk B v 0) (mk B w 0)
  rw [mk_zero_mul_mk_zero, mk_zero_eq_smul_one, d.map_smul, d.map_one_eq_zero, smul_zero,
    der_apply_mk, der_apply_mk] at h
  have := congrArg Prod.snd h
  simp at this
  rw [derVecPart_apply, derVecPart_apply]
  linear_combination -this

theorem derOfSkew_derVecPart (d : JordanDerivation R (SpinFactor R V B)) :
    derOfSkew (derVecPart d) (derVecPart_isSkew d) = d := by
  refine JordanDerivation.ext fun z => ?_
  obtain ⟨v, r⟩ := z
  change mk B (derVecPart d v) 0 = d (mk B v r)
  rw [der_apply_mk]
  rfl

/-- **Lemma 5.5** (derivations): for `V` free and `B` any symmetric bilinear form, with `2`
invertible, every derivation of `J(V, B)` is `X ⊕ 0` for a unique `X ∈ o(V, B)(R)`. -/
noncomputable def derEquivSkew :
    {X : V →ₗ[R] V // IsSkew B X} ≃ JordanDerivation R (SpinFactor R V B) where
  toFun X := derOfSkew X.1 X.2
  invFun d := ⟨derVecPart d, derVecPart_isSkew d⟩
  left_inv _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  right_inv := derOfSkew_derVecPart

end Der

end SpinFactor

end
