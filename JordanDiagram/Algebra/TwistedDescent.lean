module

public import JordanDiagram.Algebra.GaloisTwist

/-!
# Twisted Galois descent of Jordan algebras

Let `L/k` be a finite Galois extension, `B` a Jordan algebra over `k`, and
`a : Gal(L/k) → Aut(L ⊗ B)` a cocycle: `a(σ τ) = a(σ) · σ(a(τ))`, the action on `Aut(L ⊗ B)` being
transport. Then `σ ↦ a(σ) ∘ (σ ⊗ 1)` is a semilinear action of `Gal(L/k)` on `L ⊗ B` by Jordan
automorphisms over `k`; its fixed points `twistForm a` form a Jordan algebra over `k`
(`twistFixed_mul_mem`, `one_mem_twistFixed`), and Galois descent gives
`twistIso a : L ⊗ twistForm a ≅ L ⊗ B` (Speiser's lemma) with cocycle exactly `a`
(`twistAut_twistIso`). So every cocycle comes from a `k`-form of `B`.

* `JordanAlgebra.ofSubmodule`: a submodule closed under the product and containing `1` is a
  Jordan algebra.
* `jordanAut.map_one`: Jordan automorphisms fix the unit.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace JordanAlgebra

variable {R : Type*} [CommRing R] {E : Type*} [CommRing E] [Algebra R E] {A : Type*}
  [JordanAlgebra E A] [Module R A] [IsScalarTower R E A]

/-- **A submodule closed under the product and containing `1` is a Jordan algebra**: an
`R`-submodule of a Jordan algebra over an `R`-algebra `E`. -/
abbrev ofSubmodule (S : Submodule R A) (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hone : (1 : A) ∈ S) : JordanAlgebra R S :=
  letI : One S := ⟨⟨1, hone⟩⟩
  letI : Mul S := ⟨fun x y => ⟨x * y, hmul _ x.2 _ y.2⟩⟩
  letI : NatCast S := ⟨fun n => ⟨n, nsmul_one (A := A) n ▸ S.toAddSubmonoid.nsmul_mem hone n⟩⟩
  letI : IntCast S := ⟨fun n => ⟨n, zsmul_one (R := A) n ▸ S.toAddSubgroup.zsmul_mem hone n⟩⟩
  letI : NonAssocRing S := Subtype.val_injective.nonAssocRing Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  { (inferInstance : NonAssocRing S), S.module with
    smul_assoc := fun r x y => Subtype.ext (by
      change (r • (x : A)) * y = r • ((x : A) * y)
      rw [← algebraMap_smul E r (x : A), smul_mul_assoc, algebraMap_smul])
    smul_comm := fun r x y => Subtype.ext (by
      change r • ((x : A) * y) = (x : A) * (r • (y : A))
      rw [← algebraMap_smul E r (y : A), mul_smul_comm, algebraMap_smul])
    jordan_mul_comm := fun x y => Subtype.ext (jordan_mul_comm (x : A) y)
    jordan_identity := fun x y => Subtype.ext (jordan_identity (x : A) y) }

omit [Algebra R E] [Module R A] [IsScalarTower R E A] in
/-- **Jordan automorphisms fix the unit.** -/
theorem jordanAut.map_one (g : jordanAut E A) : g 1 = 1 := by
  have h : ∀ y, g 1 * y = y := fun y => by
    rw [← jordanAut.apply_inv_self g y, ← jordanAut.map_mul, one_mul]
  simpa using h 1

end JordanAlgebra

namespace JordanAlgebra.BaseChange

variable {k : Type*} [Field k] [Invertible (2 : k)] {L : Type*} [Field L] [Algebra k L]
variable {B : Type*} [JordanAlgebra k B]

variable (a : (L ≃ₐ[k] L) → jordanAut L (L ⊗[k] B))
  (ha : ∀ σ τ, a (σ * τ) = a σ * mapAut (σ : L →ₐ[k] L) (a τ))

include ha in
theorem cocycle_one : a 1 = 1 := by
  have h := ha 1 1
  rw [one_mul, show ((1 : L ≃ₐ[k] L) : L →ₐ[k] L) = AlgHom.id k L from AlgHom.ext fun _ => rfl]
    at h
  have h' : a 1 * a 1 = a 1 * 1 := by
    rw [mul_one]
    convert h.symm using 2
    exact jordanAut.ext fun x => (congrArg (fun g : jordanAut L (L ⊗[k] B) => g x)
      (mapAut_id_alg (a 1))).symm
  exact mul_left_cancel h'

/-- The twisted action `a(σ) ∘ (σ ⊗ 1)` on `L ⊗ B`. -/
def twistAct (σ : L ≃ₐ[k] L) : L ⊗[k] B →+ L ⊗[k] B where
  toFun x := a σ (gal B σ x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

theorem twistAct_apply (σ : L ≃ₐ[k] L) (x : L ⊗[k] B) : twistAct a σ x = a σ (gal B σ x) := rfl

theorem twistAct_smul (σ : L ≃ₐ[k] L) (c : L) (x : L ⊗[k] B) :
    twistAct a σ (c • x) = σ c • twistAct a σ x := by
  rw [twistAct_apply, gal_smul, ← JordanAlgebra.jordanAut.coe_mk, map_smul]
  rfl

include ha in
theorem twistAct_one (x : L ⊗[k] B) : twistAct a 1 x = x := by
  rw [twistAct_apply, gal_one, cocycle_one a ha, jordanAut.one_apply]

include ha in
theorem twistAct_mul (σ τ : L ≃ₐ[k] L) (x : L ⊗[k] B) :
    twistAct a (σ * τ) x = twistAct a σ (twistAct a τ x) := by
  simp only [twistAct_apply, ha, jordanAut.mul_apply, mapAut_apply_gal, gal_mul, gal_inv_apply]

/-- The fixed points of the twisted action, a `k`-subspace of `L ⊗ B`. -/
def twistFixed : Submodule k (L ⊗[k] B) :=
  GaloisDescent.fixedPoints (twistAct a) (twistAct_smul a)

theorem mem_twistFixed {x : L ⊗[k] B} : x ∈ twistFixed a ↔ ∀ σ, a σ (gal B σ x) = x := Iff.rfl

theorem twistFixed_mul_mem : ∀ x ∈ twistFixed a, ∀ y ∈ twistFixed a, x * y ∈ twistFixed a :=
  fun x hx y hy σ => by
    rw [twistAct_apply, gal_mul', jordanAut.map_mul]
    exact congrArg₂ (· * ·) (hx σ) (hy σ)

theorem one_mem_twistFixed : (1 : L ⊗[k] B) ∈ twistFixed a := fun σ => by
  rw [twistAct_apply, Algebra.TensorProduct.one_def, gal_tmul, map_one,
    ← Algebra.TensorProduct.one_def, JordanAlgebra.jordanAut.map_one]

/-- The `k`-form of `B` defined by the cocycle `a`. -/
abbrev twistForm : Type _ := twistFixed a

instance : JordanAlgebra k (twistForm a) :=
  JordanAlgebra.ofSubmodule (twistFixed a) (twistFixed_mul_mem a) (one_mem_twistFixed a)

theorem twistForm_coe_mul (x y : twistForm a) : ((x * y : twistForm a) : L ⊗[k] B) = x * y :=
  rfl

section Maps

variable {B' : Type*} [JordanAlgebra k B'] (a' : (L ≃ₐ[k] L) → jordanAut L (L ⊗[k] B'))

/-- A homomorphism `f : B → B'` intertwining the cocycles restricts to the twisted forms. -/
def twistMap (f : B →ₙₐ[k] B')
    (hf : ∀ σ y, a' σ (baseChangeHom L f y) = baseChangeHom L f (a σ y)) :
    twistForm a →ₙₐ[k] twistForm a' where
  toFun s := ⟨baseChangeHom L f s, fun σ => by
    change a' σ (gal B' σ (baseChangeHom L f s)) = _
    rw [gal_baseChangeHom, hf]
    exact congrArg _ (s.2 σ)⟩
  map_smul' r s := Subtype.ext (by
    change baseChangeHom L f (r • (s : L ⊗[k] B)) = r • baseChangeHom L f s
    rw [← algebraMap_smul L r (s : L ⊗[k] B), map_smul, algebraMap_smul])
  map_zero' := Subtype.ext (map_zero (baseChangeHom L f))
  map_add' s t := Subtype.ext (map_add (baseChangeHom L f) (s : L ⊗[k] B) t)
  map_mul' s t := Subtype.ext (map_mul (baseChangeHom L f) (s : L ⊗[k] B) t)

theorem coe_twistMap (f : B →ₙₐ[k] B')
    (hf : ∀ σ y, a' σ (baseChangeHom L f y) = baseChangeHom L f (a σ y)) (s : twistForm a) :
    (twistMap a a' f hf s : L ⊗[k] B') = baseChangeHom L f s := rfl

end Maps

section Iso

variable [FiniteDimensional k L] [IsGalois k L]
include ha

/-- **Twisted Galois descent**: `L ⊗ twistForm a ≅ L ⊗ B` by `c ⊗ x ↦ c • x`. -/
def twistIso : (L ⊗[k] twistForm a) ≃ⱼ[L] (L ⊗[k] B) :=
  ⟨LinearEquiv.ofBijective ((twistFixed a).subtype.liftBaseChange L)
      (GaloisDescent.bijective_liftBaseChange_fixedPoints (twistAct a) (twistAct_smul a)
        (twistAct_one a ha) (twistAct_mul a ha)),
    fun x y => by
      change (twistFixed a).subtype.liftBaseChange L (x * y) =
        (twistFixed a).subtype.liftBaseChange L x * (twistFixed a).subtype.liftBaseChange L y
      induction x with
      | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
      | tmul c s =>
        induction y with
        | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
        | tmul c' s' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.liftBaseChange_tmul,
            LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, smul_mul_smul_comm]
          rfl⟩

theorem twistIso_tmul (c : L) (s : twistForm a) :
    twistIso a ha (c ⊗ₜ s) = c • (s : L ⊗[k] B) := rfl

theorem twistIso_gal (σ : L ≃ₐ[k] L) (z : L ⊗[k] twistForm a) :
    twistIso a ha (gal (twistForm a) σ z) = a σ (gal B σ (twistIso a ha z)) := by
  induction z with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add, map_add]
  | tmul c s =>
    rw [gal_tmul, twistIso_tmul, twistIso_tmul, ← twistAct_apply, twistAct_smul]
    exact congrArg _ (s.2 σ).symm

/-- **The cocycle of the twisted form is `a`.** -/
theorem twistAut_twistIso (σ : L ≃ₐ[k] L) : twistAut (twistIso a ha) σ = a σ := by
  refine jordanAut.ext fun x => ?_
  rw [twistAut_apply, twistIso_gal, JordanEquiv.apply_symm_apply, gal_apply_inv]

/-- `twistIso` is natural in the cocycle-intertwining homomorphism. -/
theorem twistIso_naturality {B' : Type*} [JordanAlgebra k B']
    (a' : (L ≃ₐ[k] L) → jordanAut L (L ⊗[k] B'))
    (ha' : ∀ σ τ, a' (σ * τ) = a' σ * mapAut (σ : L →ₐ[k] L) (a' τ)) (f : B →ₙₐ[k] B')
    (hf : ∀ σ y, a' σ (baseChangeHom L f y) = baseChangeHom L f (a σ y))
    (z : L ⊗[k] twistForm a) :
    twistIso a' ha' (baseChangeHom L (twistMap a a' f hf) z) =
      baseChangeHom L f (twistIso a ha z) := by
  induction z with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  | tmul c s =>
    rw [baseChangeHom_tmul, twistIso_tmul, twistIso_tmul, coe_twistMap, map_smul]

end Iso

end JordanAlgebra.BaseChange
