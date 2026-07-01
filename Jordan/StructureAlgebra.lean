import Jordan.JordanAlgebra
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Structure Algebra

This file defines the `R`-module of derivations of a Jordan algebra.  A *Jordan derivation* is an
`R`-linear map `D : M → M` satisfying the Leibniz rule

    D(a * b) = a * D b + D a * b

with respect to the Jordan product.  Because a Jordan algebra is not in general an associative
`R`-algebra, the Mathlib type `Derivation R A M` (which requires `Algebra R A`) cannot be reused
here; we introduce `JordanDerivation R M` instead.
-/

namespace JordanAlgebra

variable {R M : Type*} [CommRing R] [JordanAlgebra R M]

/-- Left multiplication by a fixed element, as an `R`-linear map. -/
def lmul (a : M) : M →ₗ[R] M where
  toFun b := a * b
  map_add' b c := by rw [mul_add]
  map_smul' r b := by simpa using mul_smul_comm r a b

@[simp]
theorem lmul_apply (a b : M) : lmul (R := R) a b = a * b := rfl

@[simp]
theorem lmul_toAddMonoidEnd (a : M) :
    (lmul (R := R) a).toAddMonoidHom = AddMonoid.End.mulLeft a := rfl

@[simp]
theorem lmul_zero : lmul (R := R) (0 : M) = 0 := by
  ext b
  simp

@[simp]
theorem lmul_add (a b : M) : lmul (R := R) (a + b) = lmul (R := R) a + lmul (R := R) b := by
  ext c
  simp [add_mul]

@[simp]
theorem lmul_neg (a : M) : lmul (R := R) (-a) = -lmul (R := R) a := by
  ext b
  simp

@[simp]
theorem lmul_sub (a b : M) : lmul (R := R) (a - b) = lmul (R := R) a - lmul (R := R) b := by
  ext c
  simp [sub_eq_add_neg]

@[simp]
theorem lmul_smul (r : R) (a : M) : lmul (R := R) (r • a) = r • lmul (R := R) a := by
  ext b
  simp [smul_mul_assoc]

/-- A Jordan derivation is an `R`-linear map `D : M → M` satisfying
`D(a * b) = a * D b + D a * b`. -/
structure JordanDerivation (R M : Type*) [CommRing R] [JordanAlgebra R M] extends M →ₗ[R] M where
  leibniz' : ∀ a b : M, toLinearMap (a * b) = a * toLinearMap b + toLinearMap a * b

namespace JordanDerivation

variable {D D₁ D₂ : JordanDerivation R M} (r : R) (a b : M)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem lie_lie_lmul_lmul_lmul [Invertible (2 : R)] (x y a : M) :
    ⁅⁅AddMonoid.End.mulLeft x, AddMonoid.End.mulLeft y⁆, AddMonoid.End.mulLeft a⁆ =
      AddMonoid.End.mulLeft (⁅AddMonoid.End.mulLeft x, AddMonoid.End.mulLeft y⁆ a) := by
  let L : M → AddMonoid.End M := AddMonoid.End.mulLeft
  change ⁅⁅L x, L y⁆, L a⁆ = L (x * (y * a) - y * (x * a))
  rw [show x * (y * a) = (y * a) * x by rw [jordan_mul_comm],
    show y * (x * a) = (x * a) * y by rw [jordan_mul_comm]]
  rw [show L (y * a * x - x * a * y) = L (y * a * x) - L (x * a * y) by
    exact map_sub (AddMonoid.End.mulLeft : M →+ AddMonoid.End M) _ _]
  rw [show L (y * a * x) =
      L (y * a) * L x + L (x * a) * L y + L (y * x) * L a -
        L y * L x * L a - L a * L x * L y by
        exact lmul_mul_mul_eq (R := R) y x a,
    show L (x * a * y) =
      L (x * a) * L y + L (y * a) * L x + L (x * y) * L a -
        L x * L y * L a - L a * L y * L x by
        exact lmul_mul_mul_eq (R := R) x y a]
  rw [jordan_mul_comm y x]
  simp only [Ring.lie_def]
  noncomm_ring

/-- The commutator of two left multiplications. -/
def inner [Invertible (2 : R)] (x y : M) : JordanDerivation R M where
  toLinearMap := ⁅lmul (R := R) x, lmul (R := R) y⁆
  leibniz' a b := by
    change x * (y * (a * b)) - y * (x * (a * b)) =
      a * (x * (y * b) - y * (x * b)) + (x * (y * a) - y * (x * a)) * b
    have h := congrArg (fun f : AddMonoid.End M => f b) (lie_lie_lmul_lmul_lmul (R := R) x y a)
    change x * (y * (a * b)) - y * (x * (a * b)) -
        a * (x * (y * b) - y * (x * b)) =
      (x * (y * a) - y * (x * a)) * b at h
    rw [← h]
    abel

instance : FunLike (JordanDerivation R M) M M where
  coe D := D.toFun
  coe_injective D₁ D₂ h := by cases D₁; cases D₂; congr; exact DFunLike.coe_injective h

instance : AddMonoidHomClass (JordanDerivation R M) M M where
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

theorem toFun_eq_coe (D : JordanDerivation R M) : D.toFun = ⇑D := rfl

attribute [coe] toLinearMap

instance hasCoeToLinearMap : Coe (JordanDerivation R M) (M →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp, norm_cast]
theorem coeFn_coe (D : JordanDerivation R M) : ⇑(D : M →ₗ[R] M) = D := rfl

@[simp]
theorem inner_apply [Invertible (2 : R)] (x y a : M) :
    inner (R := R) x y a = x * (y * a) - y * (x * a) :=
  rfl

theorem coe_injective : @Function.Injective (JordanDerivation R M) (M → M) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
theorem ext (H : ∀ a, D₁ a = D₂ a) : D₁ = D₂ := DFunLike.ext _ _ H

theorem congr_fun (h : D₁ = D₂) (a : M) : D₁ a = D₂ a := DFunLike.congr_fun h a

protected theorem map_add (D : JordanDerivation R M) : D (a + b) = D a + D b :=
  map_add D a b

protected theorem map_zero (D : JordanDerivation R M) : D 0 = 0 := map_zero D

@[simp]
theorem map_smul (D : JordanDerivation R M) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a

/-- The Leibniz rule: `D(a * b) = a * D b + D a * b`. -/
@[simp]
theorem leibniz (D : JordanDerivation R M) : D (a * b) = a * D b + D a * b :=
  D.leibniz' a b

/-- Every Jordan derivation sends `1` to `0`:
`D 1 = D (1 * 1) = 1 * D 1 + D 1 * 1 = D 1 + D 1`, so cancellation gives `D 1 = 0`. -/
theorem map_one_eq_zero (D : JordanDerivation R M) : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by
    have := D.leibniz 1 1
    simp only [one_mul, mul_one] at this
    exact this
  have : D 1 + 0 = D 1 + D 1 := by rw [add_zero]; exact h
  exact (add_left_cancel this).symm

section ModuleStructure

instance : Zero (JordanDerivation R M) :=
  ⟨{ toLinearMap := 0
     leibniz' := fun a b => by simp }⟩

@[simp] theorem coe_zero : ⇑(0 : JordanDerivation R M) = 0 := rfl
theorem zero_apply : (0 : JordanDerivation R M) a = 0 := rfl

instance : Add (JordanDerivation R M) :=
  ⟨fun D₁ D₂ =>
    { toLinearMap := D₁.toLinearMap + D₂.toLinearMap
      leibniz' := fun a b => by
        simp only [LinearMap.add_apply, coeFn_coe, D₁.leibniz, D₂.leibniz, mul_add, add_mul]
        abel }⟩

@[simp] theorem coe_add (D₁ D₂ : JordanDerivation R M) : ⇑(D₁ + D₂) = D₁ + D₂ := rfl
theorem add_apply : (D₁ + D₂) a = D₁ a + D₂ a := rfl

instance : Neg (JordanDerivation R M) :=
  ⟨fun D =>
    { toLinearMap := -D.toLinearMap
      leibniz' := fun a b => by
        simp only [LinearMap.neg_apply, coeFn_coe, D.leibniz]
        rw [neg_add_rev, ← neg_mul, ← mul_neg, add_comm] }⟩

@[simp] theorem coe_neg (D : JordanDerivation R M) : ⇑(-D) = -D := rfl
theorem neg_apply (D : JordanDerivation R M) : (-D) a = -D a := rfl

instance : Sub (JordanDerivation R M) :=
  ⟨fun D₁ D₂ =>
    { toLinearMap := D₁.toLinearMap - D₂.toLinearMap
      leibniz' := fun a b => by
        simp only [LinearMap.sub_apply, coeFn_coe, D₁.leibniz, D₂.leibniz, mul_sub, sub_mul]
        abel }⟩

@[simp] theorem coe_sub (D₁ D₂ : JordanDerivation R M) : ⇑(D₁ - D₂) = D₁ - D₂ := rfl
theorem sub_apply : (D₁ - D₂) a = D₁ a - D₂ a := rfl

instance : SMul R (JordanDerivation R M) :=
  ⟨fun r D =>
    { toLinearMap := r • D.toLinearMap
      leibniz' := fun a b => by
        simp only [LinearMap.smul_apply, coeFn_coe, D.leibniz, smul_add,
          mul_smul_comm, smul_mul_assoc] }⟩

instance : SMul ℤ (JordanDerivation R M) := by
  exact SMul.comp (N:=ℤ) (M:=R) (JordanDerivation R M) (g := Int.castRingHom R)

instance : SMul ℕ (JordanDerivation R M) := by
  exact SMul.comp (N:=ℕ) (M:=R) (JordanDerivation R M) (g := Nat.castRingHom R)

@[simp] theorem coe_smul (r : R) (D : JordanDerivation R M) : ⇑(r • D) = r • ⇑D := rfl
theorem smul_apply (r : R) (D : JordanDerivation R M) : (r • D) a = r • D a := rfl

@[simp] theorem coe_nsmul (n : ℕ) (D : JordanDerivation R M) : ⇑(n • D) = n • ⇑D := by
  funext a
  change ((n : R) • D) a = n • D a
  rw [smul_apply]
  exact Nat.cast_smul_eq_nsmul R n (D a)

@[simp] theorem coe_zsmul (n : ℤ) (D : JordanDerivation R M) : ⇑(n • D) = n • ⇑D := by
  funext a
  change ((n : R) • D) a = n • D a
  rw [smul_apply]
  exact Int.cast_smul_eq_zsmul R n (D a)

instance : Inhabited (JordanDerivation R M) := ⟨0⟩

instance : AddCommGroup (JordanDerivation R M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

instance : Module R (JordanDerivation R M) :=
  Function.Injective.module R
    { toFun := (⇑), map_zero' := coe_zero, map_add' := coe_add }
    coe_injective coe_smul

end ModuleStructure

section LieAlgebraStructure

instance : Bracket (JordanDerivation R M) (JordanDerivation R M) :=
  ⟨fun D₁ D₂ =>
    { toLinearMap := ⁅(D₁ : Module.End R M), (D₂ : Module.End R M)⁆
      leibniz' := fun a b => by
        simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply, coeFn_coe,
          D₁.leibniz, D₂.leibniz, map_add]
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        rw [mul_add, add_mul]
        simp only [neg_mul, mul_neg]
        abel }⟩

@[simp]
theorem coe_lie_linearMap (D₁ D₂ : JordanDerivation R M) :
    ↑⁅D₁, D₂⁆ = ⁅(D₁ : Module.End R M), (D₂ : Module.End R M)⁆ :=
  rfl

@[simp]
theorem lie_apply (D₁ D₂ : JordanDerivation R M) (a : M) :
    ⁅D₁, D₂⁆ a = D₁ (D₂ a) - D₂ (D₁ a) :=
  rfl

instance : LieRing (JordanDerivation R M) where
  add_lie D₁ D₂ D₃ := by
    ext a
    simp only [lie_apply, add_apply, map_add]
    abel
  lie_add D₁ D₂ D₃ := by
    ext a
    simp only [lie_apply, add_apply, map_add]
    abel
  lie_self D := by
    ext a
    simp only [lie_apply, zero_apply]
    abel
  leibniz_lie D₁ D₂ D₃ := by
    ext a
    simp only [lie_apply, add_apply, map_sub]
    abel

instance : LieAlgebra R (JordanDerivation R M) where
  lie_smul r D₁ D₂ := by
    ext a
    simp only [lie_apply, smul_apply, map_smul, smul_sub]

end LieAlgebraStructure

end JordanDerivation

/-- The structure algebra as the direct sum of the algebra and its derivations. An element
`(a, D)` acts on `M` as `L_a + D`. -/
abbrev StructureAlgebra (R M : Type*) [CommRing R] [JordanAlgebra R M] :=
  M × JordanDerivation R M

namespace StructureAlgebra

variable {x y z : StructureAlgebra R M}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The natural action of the structure algebra on the underlying Jordan algebra. -/
def toEnd : StructureAlgebra R M →ₗ[R] Module.End R M where
  toFun x := lmul (R := R) x.1 + (x.2 : Module.End R M)
  map_add' x y := by
    ext a
    simp
    abel
  map_smul' r x := by
    ext a
    simp [smul_add]

@[simp]
theorem toEnd_apply (x : StructureAlgebra R M) (a : M) :
    toEnd (R := R) x a = x.1 * a + x.2 a :=
  rfl

theorem toEnd_injective : Function.Injective (toEnd (R := R) (M := M)) := by
  intro x y h
  have h_one := congrArg (fun f : Module.End R M => f 1) h
  have h_fst : x.1 = y.1 := by
    simpa [toEnd, JordanDerivation.map_one_eq_zero] using h_one
  have h_snd : x.2 = y.2 := by
    ext a
    have h_a := congrArg (fun f : Module.End R M => f a) h
    simpa [toEnd, h_fst] using h_a
  exact Prod.ext h_fst h_snd

theorem derivation_lie_lmul (D : JordanDerivation R M) (a : M) :
    ⁅(D : Module.End R M), lmul (R := R) a⁆ = lmul (R := R) (D a) := by
  ext b
  simp [Ring.lie_def, D.leibniz, sub_eq_add_neg, add_assoc]

theorem lmul_lie_derivation (a : M) (D : JordanDerivation R M) :
    ⁅lmul (R := R) a, (D : Module.End R M)⁆ = lmul (R := R) (-D a) := by
  ext b
  simp [Ring.lie_def, D.leibniz, sub_eq_add_neg]

instance [Invertible (2 : R)] : Bracket (StructureAlgebra R M) (StructureAlgebra R M) where
  bracket x y :=
    (x.2 y.1 - y.2 x.1, JordanDerivation.inner x.1 y.1 + ⁅x.2, y.2⁆)

@[simp]
theorem fst_lie [Invertible (2 : R)] (x y : StructureAlgebra R M) :
    (⁅x, y⁆ : StructureAlgebra R M).1 = x.2 y.1 - y.2 x.1 :=
  rfl

@[simp]
theorem snd_lie [Invertible (2 : R)] (x y : StructureAlgebra R M) :
    (⁅x, y⁆ : StructureAlgebra R M).2 =
      JordanDerivation.inner x.1 y.1 + ⁅x.2, y.2⁆ :=
  rfl

@[simp]
theorem toEnd_lie [Invertible (2 : R)] (x y : StructureAlgebra R M) :
    toEnd (R := R) ⁅x, y⁆ = ⁅toEnd (R := R) x, toEnd (R := R) y⁆ := by
  ext a
  simp [toEnd, Ring.lie_def, Module.End.mul_apply, JordanDerivation.lie_apply, add_mul, mul_add,
    sub_eq_add_neg]
  abel

instance [Invertible (2 : R)] : LieRing (StructureAlgebra R M) where
  add_lie x y z := toEnd_injective <| by
    simpa only [map_add, toEnd_lie] using
      (add_lie (toEnd (R := R) x) (toEnd (R := R) y) (toEnd (R := R) z))
  lie_add x y z := toEnd_injective <| by
    simpa only [map_add, toEnd_lie] using
      (lie_add (toEnd (R := R) x) (toEnd (R := R) y) (toEnd (R := R) z))
  lie_self x := toEnd_injective <| by
    simpa only [toEnd_lie, map_zero] using
      (lie_self (toEnd (R := R) x))
  leibniz_lie x y z := toEnd_injective <| by
    simpa only [toEnd_lie, map_add] using
      (leibniz_lie (toEnd (R := R) x) (toEnd (R := R) y) (toEnd (R := R) z))

instance [Invertible (2 : R)] : LieAlgebra R (StructureAlgebra R M) where
  lie_smul r x y := toEnd_injective <| by
    simpa only [map_smul, toEnd_lie] using
      (lie_smul r (toEnd (R := R) x) (toEnd (R := R) y))

/-- The distinguished Lie subalgebra of the structure algebra consisting of derivations,
embedded as pairs `(0, D)`. -/
def derivationSubalgebra [Invertible (2 : R)] : LieSubalgebra R (StructureAlgebra R M) where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    dsimp at hx hy ⊢
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro r x hx
    dsimp at hx ⊢
    rw [hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    dsimp at hx hy ⊢
    rw [hx, hy]
    simp

@[simp]
theorem mem_derivationSubalgebra_iff [Invertible (2 : R)] (x : StructureAlgebra R M) :
    x ∈ derivationSubalgebra (R := R) (M := M) ↔ x.1 = 0 :=
  Iff.rfl

/-- View a Jordan derivation as an element of the distinguished derivation subalgebra. -/
def ofDerivation [Invertible (2 : R)] (D : JordanDerivation R M) :
    derivationSubalgebra (R := R) (M := M) :=
  ⟨(0, D), rfl⟩

@[simp]
theorem ofDerivation_val [Invertible (2 : R)] (D : JordanDerivation R M) :
    (ofDerivation (R := R) (M := M) D : StructureAlgebra R M) = (0, D) :=
  rfl

end StructureAlgebra

end JordanAlgebra
