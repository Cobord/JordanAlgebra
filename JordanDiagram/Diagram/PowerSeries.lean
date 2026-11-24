module

public import JordanDiagram.Diagram.Functor
public import JordanDiagram.MathlibMissing.PowerSeriesMatrix
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Specialization from power series

For a commutative `R`-algebra `S`, the constant-term map `S⟦X⟧ → S` (`constCoeffAlg`) is split by
the inclusion of constant series (`constAlg`). For a diagram `F` with finite free nodes, consider
`G_F(S⟦X⟧) → G_F(S)`:

* `eq_one_of_mapAut_const`: for a single finite free `A`, an automorphism of `S⟦X⟧ ⊗ A` with
  trivial constant term and finite order is trivial, when `S` is torsion-free. In a basis of `A`
  it is a matrix over `S⟦X⟧` with constant term `1`, and `Matrix.eq_one_of_pow_eq_one` applies.
* `autMap_const_eq_one`: **the kernel of `G_F(S⟦X⟧) → G_F(S)` is torsion-free**.
* `injOn_autMap_const`: so every finite subgroup of `G_F(S⟦X⟧)` embeds in `G_F(S)`.
* `autMap_const_comp_autMap_C`: the specialization is split by `G_F(S) → G_F(S⟦X⟧)`.
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange TensorProduct PowerSeries

namespace JordanDiagram

noncomputable section

variable {R : Type u} [CommRing R] (S : Type u') [CommRing S] [Algebra R S]

/-- The constant-term map `S⟦X⟧ → S`, as an `R`-algebra homomorphism. -/
def constCoeffAlg : S⟦X⟧ →ₐ[R] S :=
  { constantCoeff (R := S) with
    commutes' := fun r => by
      change constantCoeff (algebraMap R S⟦X⟧ r) = _
      rw [PowerSeries.algebraMap_apply, constantCoeff_C] }

/-- The inclusion of constant series `S → S⟦X⟧`, as an `R`-algebra homomorphism. -/
def constAlg : S →ₐ[R] S⟦X⟧ :=
  { C (R := S) with
    commutes' := fun r => (PowerSeries.algebraMap_apply (R := R) (A := S) (r := r)).symm }

theorem constCoeffAlg_apply (f : S⟦X⟧) : constCoeffAlg (R := R) S f = constantCoeff f := rfl

/-- Constant term after inclusion is the identity. -/
theorem constCoeffAlg_comp_constAlg :
    (constCoeffAlg (R := R) S).comp (constAlg S) = AlgHom.id R S :=
  AlgHom.ext fun s => constantCoeff_C s

section Algebra

variable [Invertible (2 : R)] {A : Type v} [JordanAlgebra R A]
variable {S}

omit [Invertible (2 : R)] in
/-- The coordinates of the constant term are the constant terms of the coordinates. -/
theorem repr_tensorMap_const {ι : Type*} (b : Module.Basis ι R A) (x : S⟦X⟧ ⊗[R] A) (i : ι) :
    (Algebra.TensorProduct.basis S b).repr (tensorMap A (constCoeffAlg (R := R) S) x) i =
      constantCoeff ((Algebra.TensorProduct.basis S⟦X⟧ b).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, map_add, Finsupp.add_apply,
      map_add, hy]
  | tmul s a =>
    rw [tensorMap_tmul, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul]
    rw [constCoeffAlg_apply, PowerSeries.algebraMap_apply, constantCoeff_C]

variable [Module.Free R A] [Module.Finite R A]

/-- **Specialization from power series, one algebra**: for a finite free `A` and a torsion-free
`S`, an automorphism of `S⟦X⟧ ⊗[R] A` with trivial constant term and finite order is trivial. -/
theorem eq_one_of_mapAut_const [IsAddTorsionFree S] (g : jordanAut S⟦X⟧ (S⟦X⟧ ⊗[R] A))
    (h0 : mapAut (constCoeffAlg (R := R) S) g = 1) {k : ℕ} (hk : k ≠ 0) (hg : g ^ k = 1) :
    g = 1 := by
  classical
  set b := Module.Free.chooseBasis R A
  set B := Algebra.TensorProduct.basis S⟦X⟧ b
  set B0 := Algebra.TensorProduct.basis S b
  set f : S⟦X⟧ ⊗[R] A →ₗ[S⟦X⟧] S⟦X⟧ ⊗[R] A :=
    (g : S⟦X⟧ ⊗[R] A ≃ₗ[S⟦X⟧] S⟦X⟧ ⊗[R] A).toLinearMap
  set M := LinearMap.toMatrix B B f
  have hfk : f ^ k = 1 := LinearMap.ext fun x => by
    have hx : ((g ^ k : jordanAut S⟦X⟧ (S⟦X⟧ ⊗[R] A)) :
        S⟦X⟧ ⊗[R] A ≃ₗ[S⟦X⟧] S⟦X⟧ ⊗[R] A) x = x := by
      have := congrArg (fun h : jordanAut S⟦X⟧ (S⟦X⟧ ⊗[R] A) => h x) hg
      simpa only [jordanAut.one_apply] using this
    rw [SubgroupClass.coe_pow, LinearEquiv.pow_apply] at hx
    rw [Module.End.pow_apply, Module.End.one_apply]
    exact hx
  have hMk : M ^ k = 1 := by
    change LinearMap.toMatrixAlgEquiv B f ^ k = 1
    rw [← map_pow, hfk, map_one]
  have hM0 : (constantCoeff (R := S)).mapMatrix M = 1 := by
    ext i j
    change constantCoeff (LinearMap.toMatrix B B f i j) = _
    rw [LinearMap.toMatrix_apply, ← repr_tensorMap_const]
    have hB : tensorMap A (constCoeffAlg (R := R) S) (B j) = B0 j := by
      rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, tensorMap_tmul,
        map_one]
    have key : tensorMap A (constCoeffAlg (R := R) S) (f (B j)) = B0 j := by
      change tensorMap A (constCoeffAlg (R := R) S) (g (B j)) = _
      rw [← mapAut_tensorMap, h0, hB]
      rfl
    rw [key, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hM : M = 1 := Matrix.eq_one_of_pow_eq_one M hM0 hk hMk
  have hf : f = LinearMap.id :=
    (LinearMap.toMatrix B B).injective (by change M = _; rw [hM, LinearMap.toMatrix_id])
  exact jordanAut.ext fun x => LinearMap.congr_fun hf x

end Algebra

section Diagram

variable [Invertible (2 : R)] {I : Type w} [Category.{w'} I] (F : JordanDiagram.{u, v} R I)

/-- **Specialization from power series**: if every node of `F` is finite free and `S` is
torsion-free, the kernel of `G_F(S⟦X⟧) → G_F(S)` is torsion-free. -/
theorem autMap_const_eq_one [∀ i, Module.Free R (F.obj i)] [∀ i, Module.Finite R (F.obj i)]
    [IsAddTorsionFree S] (g : (F.baseChange S⟦X⟧).autGroup)
    (h0 : autMap F (constCoeffAlg (R := R) S) g = 1) {k : ℕ} (hk : k ≠ 0) (hg : g ^ k = 1) :
    g = 1 :=
  Subtype.ext (funext fun i => eq_one_of_mapAut_const (g.1 i)
    (congrArg (fun h : (F.baseChange S).autGroup => h.1 i) h0) hk
    (by simpa using congrArg (fun h : (F.baseChange S⟦X⟧).autGroup => h.1 i) hg))

/-- Every finite subgroup of `G_F(S⟦X⟧)` embeds in `G_F(S)` under specialization. -/
theorem injOn_autMap_const [∀ i, Module.Free R (F.obj i)] [∀ i, Module.Finite R (F.obj i)]
    [IsAddTorsionFree S] (H : Subgroup (F.baseChange S⟦X⟧).autGroup) [Finite H] :
    Set.InjOn (autMap F (constCoeffAlg (R := R) S)) H := by
  intro x hx y hy hxy
  set z : H := ⟨x⁻¹ * y, H.mul_mem (H.inv_mem hx) hy⟩
  have hz : (z : (F.baseChange S⟦X⟧).autGroup) = 1 := by
    refine autMap_const_eq_one S F z ?_ (isOfFinOrder_of_finite z).orderOf_pos.ne' ?_
    · change autMap F _ (x⁻¹ * y) = 1
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    · rw [← SubgroupClass.coe_pow, pow_orderOf_eq_one]
      rfl
  have : x⁻¹ * y = 1 := hz
  rw [inv_mul_eq_one] at this
  exact this

/-- Specialization is split by the inclusion of constant series. -/
theorem autMap_const_comp_autMap_C :
    (autMap F (constCoeffAlg (R := R) S)).comp (autMap F (constAlg S)) = MonoidHom.id _ := by
  rw [← autMap_comp, constCoeffAlg_comp_constAlg, autMap_id]

end Diagram

end

end JordanDiagram
