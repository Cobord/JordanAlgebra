module

public import JordanDiagram.Algebra.Automorphism
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# Automorphisms are determined on generating sets

`jordanAut.ext_of_adjoin_eq_top`: a Jordan automorphism of a single algebra is determined by its
values on a set that generates the algebra as a (non-unital) subalgebra. This is the
single-algebra input to the statement about generating configurations.
-/

@[expose] public section

namespace JordanAlgebra.jordanAut

variable {R A : Type*} [CommRing R] [JordanAlgebra R A]

/-- A Jordan automorphism is determined by its values on a generating set. -/
theorem ext_of_adjoin_eq_top {S : Set A} (hS : NonUnitalAlgebra.adjoin R S = ⊤)
    {g h : jordanAut R A} (heq : ∀ x ∈ S, g x = h x) : g = h := by
  ext y
  have hy : y ∈ NonUnitalAlgebra.adjoin R S := hS ▸ trivial
  induction hy using NonUnitalAlgebra.adjoin_induction with
  | mem x hx => exact heq x hx
  | add x y _ _ hx hy =>
    change (g : A ≃ₗ[R] A) (x + y) = (h : A ≃ₗ[R] A) (x + y)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | zero =>
    change (g : A ≃ₗ[R] A) 0 = (h : A ≃ₗ[R] A) 0
    rw [map_zero, map_zero]
  | mul x y _ _ hx hy => rw [jordanAut.map_mul, jordanAut.map_mul, hx, hy]
  | smul r x _ hx =>
    change (g : A ≃ₗ[R] A) (r • x) = (h : A ≃ₗ[R] A) (r • x)
    rw [map_smul, map_smul]
    exact congrArg (r • ·) hx

end JordanAlgebra.jordanAut
