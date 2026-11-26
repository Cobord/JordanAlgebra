module

public import JordanDiagram.Algebra.Functor
public import JordanDiagram.Algebra.Equiv
public import JordanDiagram.MathlibMissing.GaloisDescent

/-!
# Galois twists of Jordan algebras

Let `L/k` be a field extension and `A`, `B` Jordan algebras over `k`. The Galois group acts on
`L ⊗[k] A` through the first factor, `σ ⊗ 1` (`gal A σ`), semilinearly and multiplicatively; the
induced action on `Aut(L ⊗ A)` by conjugation is transport along `σ` (`mapAut_apply_gal`).

For an `L`-isomorphism `θ : L ⊗ A ≅ L ⊗ B`, the automorphisms
`twistAut θ σ = θ (σ ⊗ 1) θ⁻¹ (σ⁻¹ ⊗ 1)` of `L ⊗ B` form a cocycle: `twistAut θ (σ τ) =
twistAut θ σ · σ(twistAut θ τ)` (`twistAut_mul`). Changing `θ` by isomorphisms changes the cocycle
by a coboundary (`twistAut_baseChange_trans`).
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace JordanAlgebra.BaseChange

variable {k : Type*} [Field k] [Invertible (2 : k)] {L : Type*} [Field L] [Algebra k L]
variable {A B C : Type*} [JordanAlgebra k A] [JordanAlgebra k B] [JordanAlgebra k C]

section Gal

variable (A) in
/-- `σ ⊗ 1` on `L ⊗[k] A`. -/
abbrev gal (σ : L ≃ₐ[k] L) : L ⊗[k] A →ₗ[k] L ⊗[k] A := tensorMap A (σ : L →ₐ[k] L)

omit [Invertible (2 : k)] in
theorem gal_tmul (σ : L ≃ₐ[k] L) (c : L) (a : A) : gal A σ (c ⊗ₜ a) = σ c ⊗ₜ a := rfl

omit [Invertible (2 : k)] in
theorem gal_mul (σ τ : L ≃ₐ[k] L) (x : L ⊗[k] A) : gal A (σ * τ) x = gal A σ (gal A τ x) := by
  unfold gal
  rw [show ((σ * τ : L ≃ₐ[k] L) : L →ₐ[k] L) = (σ : L →ₐ[k] L).comp τ from AlgHom.ext fun _ => rfl]
  exact tensorMap_comp _ _ x

omit [Invertible (2 : k)] in
theorem gal_one (x : L ⊗[k] A) : gal A 1 x = x := by
  unfold gal
  rw [show ((1 : L ≃ₐ[k] L) : L →ₐ[k] L) = AlgHom.id k L from AlgHom.ext fun _ => rfl]
  exact tensorMap_id x

omit [Invertible (2 : k)] in
@[simp]
theorem gal_inv_apply (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) : gal A σ⁻¹ (gal A σ x) = x := by
  rw [← gal_mul, inv_mul_cancel, gal_one]

omit [Invertible (2 : k)] in
@[simp]
theorem gal_apply_inv (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) : gal A σ (gal A σ⁻¹ x) = x := by
  rw [← gal_mul, mul_inv_cancel, gal_one]

omit [Invertible (2 : k)] in
theorem gal_smul (σ : L ≃ₐ[k] L) (c : L) (x : L ⊗[k] A) :
    gal A σ (c • x) = σ c • gal A σ x :=
  tensorMap_smul _ _ _

omit [Invertible (2 : k)] in
theorem gal_mul' (σ : L ≃ₐ[k] L) (x y : L ⊗[k] A) : gal A σ (x * y) = gal A σ x * gal A σ y :=
  tensorMap_mul _ _ _

omit [Invertible (2 : k)] in
theorem gal_baseChangeHom (σ : L ≃ₐ[k] L) (f : A →ₙₐ[k] B) (x : L ⊗[k] A) :
    gal B σ (baseChangeHom L f x) = baseChangeHom L f (gal A σ x) :=
  tensorMap_baseChangeHom _ _ _

/-- The Galois action on `Aut(L ⊗ A)` by transport is conjugation by `σ ⊗ 1`. -/
theorem mapAut_apply_gal (σ : L ≃ₐ[k] L) (g : jordanAut L (L ⊗[k] A)) (x : L ⊗[k] A) :
    mapAut (σ : L →ₐ[k] L) g x = gal A σ (g (gal A σ⁻¹ x)) := by
  conv_lhs => rw [← gal_apply_inv σ x]
  exact mapAut_tensorMap _ g _

omit [Invertible (2 : k)] in
@[simp]
theorem gal_incl (σ : L ≃ₐ[k] L) (a : A) : gal A σ (incl L a) = incl L a := by
  rw [incl, gal_tmul, map_one]

omit [Invertible (2 : k)] in
theorem inv_apply_apply (σ : L ≃ₐ[k] L) (c : L) : σ (σ⁻¹ c) = c :=
  AlgEquiv.apply_symm_apply σ c

end Gal

section Twist

/-- The automorphism `θ (σ ⊗ 1) θ⁻¹ (σ⁻¹ ⊗ 1)` of `L ⊗ B`, for `θ : L ⊗ A ≅ L ⊗ B`. -/
def twistAut (θ : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] B)) (σ : L ≃ₐ[k] L) : jordanAut L (L ⊗[k] B) :=
  ⟨{ toFun := fun x => θ (gal A σ (θ.symm (gal B σ⁻¹ x)))
     invFun := fun x => gal B σ (θ (gal A σ⁻¹ (θ.symm x)))
     map_add' := fun x y => by simp only [map_add]
     map_smul' := fun c x => by
       simp only [gal_smul, RingHom.id_apply]
       rw [← JordanEquiv.coe_toLinearEquiv θ.symm, LinearEquiv.map_smul,
         JordanEquiv.coe_toLinearEquiv, gal_smul, inv_apply_apply,
         ← JordanEquiv.coe_toLinearEquiv θ, LinearEquiv.map_smul]
     left_inv := fun x => by simp
     right_inv := fun x => by simp },
    fun x y => by
      change θ (gal A σ (θ.symm (gal B σ⁻¹ (x * y)))) =
        θ (gal A σ (θ.symm (gal B σ⁻¹ x))) * θ (gal A σ (θ.symm (gal B σ⁻¹ y)))
      rw [gal_mul', θ.symm.map_mul, gal_mul', θ.map_mul]⟩

@[simp]
theorem twistAut_apply (θ : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] B)) (σ : L ≃ₐ[k] L) (x : L ⊗[k] B) :
    twistAut θ σ x = θ (gal A σ (θ.symm (gal B σ⁻¹ x))) := rfl

/-- **The cocycle identity** `a(σ τ) = a(σ) · σ(a(τ))`, the action on `Aut(L ⊗ B)` being
transport. -/
theorem twistAut_mul (θ : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] B)) (σ τ : L ≃ₐ[k] L) :
    twistAut θ (σ * τ) = twistAut θ σ * mapAut (σ : L →ₐ[k] L) (twistAut θ τ) := by
  refine jordanAut.ext fun x => ?_
  simp only [jordanAut.mul_apply, twistAut_apply, mapAut_apply_gal, gal_inv_apply,
    JordanEquiv.symm_apply_apply, mul_inv_rev, gal_mul]

/-- Scalar extension of a Jordan isomorphism. -/
def baseChangeEquiv (e : A ≃ⱼ[k] B) : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] B) :=
  ⟨LinearEquiv.ofLinearMap (toLin (baseChangeHom L e.toHom))
      (toLin (baseChangeHom L e.symm.toHom))
      (ext_one_tmul fun b => by simp [toLin_apply, baseChangeHom_tmul])
      (ext_one_tmul fun a => by simp [toLin_apply, baseChangeHom_tmul]),
    fun x y => map_mul (baseChangeHom L e.toHom) x y⟩

theorem baseChangeEquiv_tmul (e : A ≃ⱼ[k] B) (c : L) (a : A) :
    baseChangeEquiv e (c ⊗ₜ a) = c ⊗ₜ e a := rfl

theorem baseChangeEquiv_symm_apply (e : A ≃ⱼ[k] B) (x : L ⊗[k] B) :
    (baseChangeEquiv e).symm x = baseChangeHom L e.symm.toHom x := rfl

theorem gal_baseChangeEquiv (σ : L ≃ₐ[k] L) (e : A ≃ⱼ[k] B) (x : L ⊗[k] A) :
    gal B σ (baseChangeEquiv e x) = baseChangeEquiv e (gal A σ x) :=
  gal_baseChangeHom σ e.toHom x

theorem gal_baseChangeEquiv_symm (σ : L ≃ₐ[k] L) (e : A ≃ⱼ[k] B) (x : L ⊗[k] B) :
    gal A σ ((baseChangeEquiv e).symm x) = (baseChangeEquiv e).symm (gal B σ x) :=
  gal_baseChangeHom σ e.symm.toHom x

/-- Precomposing `θ` with the scalar extension of a `k`-isomorphism does not change the cocycle. -/
theorem twistAut_baseChange_trans (e : A ≃ⱼ[k] B) (θ : (L ⊗[k] B) ≃ⱼ[L] (L ⊗[k] C))
    (σ : L ≃ₐ[k] L) : twistAut ((baseChangeEquiv e).trans θ) σ = twistAut θ σ := by
  refine jordanAut.ext fun x => ?_
  change θ (baseChangeEquiv e (gal A σ ((baseChangeEquiv e).symm (θ.symm (gal C σ⁻¹ x))))) = _
  rw [gal_baseChangeEquiv_symm, JordanEquiv.apply_symm_apply]
  rfl

/-- Postcomposing `θ` with an automorphism `c` changes the cocycle by the coboundary of `c`. -/
theorem twistAut_trans_ofAut (θ : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] B)) (c : jordanAut L (L ⊗[k] B))
    (σ : L ≃ₐ[k] L) :
    twistAut (θ.trans (JordanEquiv.ofAut c)) σ =
      c * twistAut θ σ * mapAut (σ : L →ₐ[k] L) c⁻¹ := by
  refine jordanAut.ext fun x => ?_
  simp only [jordanAut.mul_apply, twistAut_apply, mapAut_apply_gal, gal_inv_apply]
  rfl

/-- Two isomorphisms with the same cocycle differ by a Galois-equivariant isomorphism. -/
theorem gal_comm_of_twistAut_eq (χ : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] C))
    (θ : (L ⊗[k] B) ≃ⱼ[L] (L ⊗[k] C)) (σ : L ≃ₐ[k] L) (h : twistAut χ σ = twistAut θ σ)
    (x : L ⊗[k] A) : θ.symm (χ (gal A σ x)) = gal B σ (θ.symm (χ x)) := by
  have := congrArg (fun g : jordanAut L (L ⊗[k] C) => g (gal C σ (χ x))) h
  simp only [twistAut_apply, gal_inv_apply, JordanEquiv.symm_apply_apply] at this
  rw [this, JordanEquiv.symm_apply_apply]

end Twist

section Descent

variable [FiniteDimensional k L] [IsGalois k L]

omit [Invertible (2 : k)] [FiniteDimensional k L] [IsGalois k L] in
/-- Over a field, `a ↦ 1 ⊗ a : A → L ⊗[k] A` is injective. -/
theorem incl_injective_field : Function.Injective (incl (A := A) L) := by
  classical
  intro a a' h
  set b := Module.Basis.ofVectorSpace k A
  apply b.repr.injective
  ext i
  have := congrArg (fun x => (b.baseChange L).repr x i) h
  simp only [incl, Module.Basis.baseChange_repr_tmul] at this
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at this
  exact (algebraMap k L).injective this

omit [Invertible (2 : k)] in
/-- An element of `L ⊗ A` fixed by every `σ ⊗ 1` is `1 ⊗ a` for a unique `a`. -/
theorem exists_incl_of_fixed (x : L ⊗[k] A) (hx : ∀ σ : L ≃ₐ[k] L, gal A σ x = x) :
    ∃ a : A, x = incl L a :=
  GaloisDescent.exists_tmul_of_forall_rTensor_eq x hx

/-- **Descent of isomorphisms**: an `L`-isomorphism `L ⊗ A ≅ L ⊗ B` commuting with every `σ ⊗ 1`
is the scalar extension of a `k`-isomorphism `A ≅ B`. -/
theorem exists_baseChangeEquiv_eq (Ψ : (L ⊗[k] A) ≃ⱼ[L] (L ⊗[k] B))
    (hΨ : ∀ (σ : L ≃ₐ[k] L) x, Ψ (gal A σ x) = gal B σ (Ψ x)) :
    ∃ e : A ≃ⱼ[k] B, ∀ x, baseChangeEquiv e x = Ψ x := by
  have hΨ' : ∀ (σ : L ≃ₐ[k] L) y, Ψ.symm (gal B σ y) = gal A σ (Ψ.symm y) := fun σ y => by
    apply Ψ.injective
    rw [JordanEquiv.apply_symm_apply, hΨ, JordanEquiv.apply_symm_apply]
  have hfix : ∀ a : A, ∃ b : B, Ψ (incl L a) = incl L b := fun a =>
    exists_incl_of_fixed _ fun σ => by rw [← hΨ, gal_incl]
  have hfix' : ∀ b : B, ∃ a : A, Ψ.symm (incl L b) = incl L a := fun b =>
    exists_incl_of_fixed _ fun σ => by rw [← hΨ', gal_incl]
  choose f hf using hfix
  choose g hg using hfix'
  have hinjB := incl_injective_field (A := B) (L := L)
  have hinjA := incl_injective_field (A := A) (L := L)
  have hfg : ∀ b, f (g b) = b := fun b => hinjB (by rw [← hf, ← hg, JordanEquiv.apply_symm_apply])
  have hgf : ∀ a, g (f a) = a := fun a => hinjA (by rw [← hg, ← hf, JordanEquiv.symm_apply_apply])
  let e : A ≃ⱼ[k] B :=
    ⟨{ toFun := f
       invFun := g
       map_add' := fun a a' => hinjB (by rw [← hf, incl_add, map_add, hf, hf, incl_add])
       map_smul' := fun r a => hinjB (by
         rw [← hf, RingHom.id_apply, incl_smul, ← algebraMap_smul L r,
           ← JordanEquiv.coe_toLinearEquiv, LinearEquiv.map_smul, JordanEquiv.coe_toLinearEquiv,
           hf, algebraMap_smul, incl_smul])
       left_inv := hgf
       right_inv := hfg },
      fun a a' => hinjB (by
        change incl L (f (a * a')) = incl L (f a * f a')
        rw [← hf, incl_mul, Ψ.map_mul, hf, hf, incl_mul])⟩
  refine ⟨e, fun x => ?_⟩
  have h : (baseChangeEquiv e).toLinearEquiv.toLinearMap = Ψ.toLinearEquiv.toLinearMap :=
    ext_one_tmul fun a => (hf a).symm
  exact LinearMap.congr_fun h x

end Descent

end JordanAlgebra.BaseChange
