module

public import JordanDiagram.Algebra.BaseChange
public import JordanDiagram.Algebra.Equiv

/-!
# Scalar extension in towers (the coherences `β_f`)

For `R → S → T`, scalar extension in two steps agrees with scalar extension in one:
`cancelJordanEquiv : T ⊗[S] (S ⊗[R] A) ≃ⱼ[T] T ⊗[R] A` is a Jordan isomorphism. This is the
coherence `β_f` for `f : S → T` of the scalar-extension family `S ↦ S ⊗[R] A`.

Through it, an automorphism of `S ⊗[R] A` extends to one of `T ⊗[R] A` (`autTower`). This map
extends `Aut(A) → Aut(S ⊗ A)`: `autTower ∘ baseChangeAut S = baseChangeAut T`
(`autTower_baseChangeAut`). This is the functoriality of `G_F` for one-node
diagrams; `JordanDiagram.autTowerDiagram` does the same for diagrams.

`[Invertible (2 : S)]` is taken as a separate hypothesis. It follows from `Invertible (2 : R)`,
and since `Invertible` is a subsingleton nothing depends on the choice.
-/

@[expose] public section

open TensorProduct

namespace JordanAlgebra.BaseChange

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {S : Type*} [CommRing S] [Algebra R S] [Invertible (2 : S)]
variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {A : Type*} [JordanAlgebra R A]

omit [Invertible (2 : S)] in
theorem cancel_mul (x y : T ⊗[S] (S ⊗[R] A)) :
    AlgebraTensorModule.cancelBaseChange R S T T A (x * y) =
      AlgebraTensorModule.cancelBaseChange R S T T A x *
        AlgebraTensorModule.cancelBaseChange R S T T A y := by
  induction x with
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]
  | tmul t x =>
    induction y with
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | tmul t' y =>
      induction x with
      | add x z hx hz => simp only [TensorProduct.tmul_add, add_mul, map_add, hx, hz]
      | tmul s a =>
        induction y with
        | add y z hy hz => simp only [TensorProduct.tmul_add, mul_add, map_add, hy, hz]
        | tmul s' b =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul,
            AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, map_mul]
          congr 1
          ring

variable (R S T A) in
/-- The coherence isomorphism `T ⊗[S] (S ⊗[R] A) ≃ⱼ[T] T ⊗[R] A`. -/
noncomputable def cancelJordanEquiv : T ⊗[S] (S ⊗[R] A) ≃ⱼ[T] T ⊗[R] A :=
  ⟨AlgebraTensorModule.cancelBaseChange R S T T A, cancel_mul⟩

@[simp]
theorem cancelJordanEquiv_tmul (t : T) (s : S) (a : A) :
    cancelJordanEquiv R S T A (t ⊗ₜ (s ⊗ₜ a)) = (s • t) ⊗ₜ a := rfl

@[simp]
theorem cancelJordanEquiv_symm_tmul (t : T) (a : A) :
    (cancelJordanEquiv R S T A).symm (t ⊗ₜ a) = t ⊗ₜ ((1 : S) ⊗ₜ a) := rfl

/-- Conjugating by a Jordan isomorphism, as a group isomorphism of automorphism groups. -/
def conjAut {X Y : Type*} [JordanAlgebra T X] [JordanAlgebra T Y] (e : X ≃ⱼ[T] Y) :
    jordanAut T X →* jordanAut T Y where
  toFun g := ((e.symm.trans (JordanEquiv.ofAut g)).trans e).toAut
  map_one' := jordanAut.ext fun y => JordanEquiv.apply_symm_apply e y
  map_mul' g h := jordanAut.ext fun y => by
    change e (g (h (e.symm y))) = e (g (e.symm (e (h (e.symm y)))))
    rw [JordanEquiv.symm_apply_apply]

theorem conjAut_apply {X Y : Type*} [JordanAlgebra T X] [JordanAlgebra T Y] (e : X ≃ⱼ[T] Y)
    (g : jordanAut T X) (y : Y) : conjAut e g y = e (g (e.symm y)) := rfl

variable (S T) in
/-- Extending automorphisms from `S ⊗[R] A` to `T ⊗[R] A`: `g ↦ β ∘ (id_T ⊗ g) ∘ β⁻¹`. -/
noncomputable def autTower : jordanAut S (S ⊗[R] A) →* jordanAut T (T ⊗[R] A) :=
  (conjAut (cancelJordanEquiv R S T A)).comp (baseChangeAut T)

/-- **Functoriality, one node**: extending `Aut(A) → Aut(S ⊗ A)` further to
`T` is extending `Aut(A) → Aut(T ⊗ A)` directly. -/
theorem autTower_baseChangeAut (h : jordanAut R A) :
    autTower S T (baseChangeAut S h) = baseChangeAut T h := by
  refine jordanAut.ext fun x => ?_
  induction x with
  | add x y hx hy =>
    change ((autTower S T (baseChangeAut S h) : jordanAut T (T ⊗[R] A)) :
        T ⊗[R] A ≃ₗ[T] T ⊗[R] A) (x + y) =
      ((baseChangeAut T h : jordanAut T (T ⊗[R] A)) : T ⊗[R] A ≃ₗ[T] T ⊗[R] A) (x + y)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul t a =>
    change cancelJordanEquiv R S T A (t ⊗ₜ ((1 : S) ⊗ₜ h a)) = t ⊗ₜ h a
    rw [cancelJordanEquiv_tmul, one_smul]

/-- The coherence isomorphism commutes with scalar extension of morphisms. -/
theorem cancelJordanEquiv_baseChangeHom {B : Type*} [JordanAlgebra R B] (f : A →ₙₐ[R] B)
    (x : T ⊗[S] (S ⊗[R] A)) :
    cancelJordanEquiv R S T B (baseChangeHom T (baseChangeHom S f) x) =
      baseChangeHom T f (cancelJordanEquiv R S T A x) := by
  induction x with
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, ← map_add, ← map_add]
  | tmul t x =>
    induction x with
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, ← map_add, ← map_add]
    | tmul s a => rfl

end JordanAlgebra.BaseChange
