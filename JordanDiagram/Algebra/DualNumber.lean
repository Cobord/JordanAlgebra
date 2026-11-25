module

public import JordanDiagram.Algebra.SquareZero
public import JordanDiagram.Algebra.Functor
public import Mathlib.Algebra.DualNumber

/-!
# Derivations as automorphisms over the dual numbers

For a Jordan algebra `A` over `R` (with `2` invertible) and a commutative `R`-algebra `S`, let
`S[ε] = S ⊕ S ε` be the dual numbers. Write `inl : S → S[ε]` and `fst : S[ε] → S` for the
inclusion and the reduction `ε ↦ 0`. A Jordan derivation `D` of `S ⊗[R] A` gives the automorphism
`1 + ε D` of `S[ε] ⊗[R] A` (`D` extended `S[ε]`-linearly), which reduces to the identity modulo `ε`.
Conversely every automorphism `g` reducing to the identity is of this form, with
`D(x) = (ε-component of g(x))`:

* `sndTensor`: the `ε`-component `S[ε] ⊗[R] A → S ⊗[R] A`, and the decomposition
  `z = inl(fst z) + ε inl(snd z)` (`eq_inl_add_eps_smul`);
* `mapAut_sqZeroAut`: transport of `1 + e D` along `φ` is `1 + φ(e) φ_*(D)`, so `1 + ε D` reduces
  to the identity (`mapAut_fst_sqZeroAut`);
* `derOfDual g hg`: the derivation read off from an automorphism `g` reducing to the identity,
  with `sqZeroAut_derOfDual` and `derOfDual_sqZeroAut` showing that the two constructions are
  mutually inverse, and `derOfDual_comm` its compatibility with scalar-extended homomorphisms.
-/

@[expose] public section

open TensorProduct DualNumber TrivSqZeroExt

namespace JordanAlgebra.BaseChange

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {A : Type*} [JordanAlgebra R A] {B : Type*} [JordanAlgebra R B]
variable {S : Type*} [CommRing S] [Algebra R S]
variable {T : Type*} [CommRing T] [Algebra R T]

section Transport

/-- Transport of `1 + e D` along `φ` is `1 + φ(e) φ_*(D)`. -/
theorem mapAut_sqZeroAut (φ : S →ₐ[R] T) (e : S) (he : e * e = 0)
    (d : JordanDerivation S (S ⊗[R] A)) :
    mapAut φ (sqZeroAut e he d) =
      sqZeroAut (φ e) (by rw [← map_mul, he, map_zero]) (mapDer φ d) := by
  refine Subtype.ext (LinearEquiv.toLinearMap_injective (ext_one_tmul fun a => ?_))
  change mapLin φ (sqZeroLin e d) _ = sqZeroLin (φ e) (mapDer φ d) _
  rw [mapLin_one_tmul, sqZeroLin_apply, sqZeroLin_apply, map_add, tensorMap_smul,
    tensorMap_one_tmul, mapDer_apply, mapLin_one_tmul]
  rfl

end Transport

variable (R S) in
/-- The inclusion `inl : S → S[ε]`. -/
noncomputable abbrev inlS : S →ₐ[R] DualNumber S := TrivSqZeroExt.inlAlgHom R S S

variable (R S) in
/-- The reduction `fst : S[ε] → S`, `ε ↦ 0`. -/
noncomputable abbrev fstS : DualNumber S →ₐ[R] S := TrivSqZeroExt.fstHom R S S

omit [Invertible (2 : R)] in
theorem tensorMap_fstS_inlS (x : S ⊗[R] A) :
    tensorMap A (fstS R S) (tensorMap A (inlS R S) x) = x := by
  rw [← tensorMap_comp, show (fstS R S).comp (inlS R S) = AlgHom.id R S from
    AlgHom.ext fun _ => rfl, tensorMap_id]

/-! `Module R S[ε]` comes both from `TrivSqZeroExt.module` and from the algebra structure; the
`S[ε]`-action on `S[ε] ⊗[R] A` is built over the second, so the generic `smul_add` and `zero_smul`
do not rewrite there syntactically. These restatements are proved by unification instead. -/

omit [Invertible (2 : R)] in
private theorem dual_smul_add (c : DualNumber S) (x y : DualNumber S ⊗[R] A) :
    c • (x + y) = c • x + c • y :=
  smul_add c x y

omit [Invertible (2 : R)] in
private theorem dual_zero_smul (x : DualNumber S ⊗[R] A) : (0 : DualNumber S) • x = 0 :=
  zero_smul (DualNumber S) x

variable (A) in
/-- The `ε`-component `S[ε] ⊗[R] A → S ⊗[R] A`, `(s + s' ε) ⊗ a ↦ s' ⊗ a`. -/
noncomputable def sndTensor : DualNumber S ⊗[R] A →ₗ[R] S ⊗[R] A :=
  TensorProduct.map ((TrivSqZeroExt.sndHom S S).restrictScalars R) LinearMap.id

omit [Invertible (2 : R)] in
@[simp]
theorem sndTensor_tmul (t : DualNumber S) (a : A) : sndTensor A (t ⊗ₜ a) = t.snd ⊗ₜ a := rfl

omit [Invertible (2 : R)] in
theorem sndTensor_tensorMap_inlS (x : S ⊗[R] A) : sndTensor A (tensorMap A (inlS R S) x) = 0 := by
  induction x with
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul s a => rw [tensorMap_tmul, sndTensor_tmul, TrivSqZeroExt.inlAlgHom_apply, snd_inl,
      zero_tmul]

omit [Invertible (2 : R)] in
theorem sndTensor_eps_smul (x : S ⊗[R] A) :
    sndTensor A ((ε : DualNumber S) • tensorMap A (inlS R S) x) = x := by
  induction x with
  | add x y hx hy => rw [map_add, dual_smul_add, map_add, hx, hy]
  | tmul s a =>
    rw [tensorMap_tmul, TensorProduct.smul_tmul', sndTensor_tmul, smul_eq_mul, DualNumber.snd_mul,
      fst_eps, snd_eps, TrivSqZeroExt.inlAlgHom_apply, fst_inl, snd_inl, zero_mul, one_mul,
      zero_add]

omit [Invertible (2 : R)] in
theorem sndTensor_inlS_smul (s : S) (z : DualNumber S ⊗[R] A) :
    sndTensor A (inlS R S s • z) = s • sndTensor A z := by
  induction z with
  | add x y hx hy => rw [dual_smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul t a =>
    rw [TensorProduct.smul_tmul', sndTensor_tmul, sndTensor_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, DualNumber.snd_mul, TrivSqZeroExt.inlAlgHom_apply, fst_inl, snd_inl,
      zero_mul, add_zero]

omit [Invertible (2 : R)] in
/-- The decomposition `z = inl(fst z) + ε inl(snd z)` of `S[ε] ⊗[R] A`. -/
theorem eq_inl_add_eps_smul (z : DualNumber S ⊗[R] A) :
    z = tensorMap A (inlS R S) (tensorMap A (fstS R S) z) +
      (ε : DualNumber S) • tensorMap A (inlS R S) (sndTensor A z) := by
  induction z with
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, dual_smul_add, add_add_add_comm, ← hx, ← hy]
  | tmul t a =>
    rw [tensorMap_tmul, tensorMap_tmul, sndTensor_tmul, tensorMap_tmul, TensorProduct.smul_tmul',
      ← add_tmul]
    congr 1
    ext <;> simp

omit [Invertible (2 : R)] in
theorem sndTensor_baseChangeHom (f : A →ₙₐ[R] B) (z : DualNumber S ⊗[R] A) :
    sndTensor B (baseChangeHom (DualNumber S) f z) = baseChangeHom S f (sndTensor A z) := by
  induction z with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul t a => rfl

/-- `1 + ε D` reduces to the identity modulo `ε`. -/
theorem mapAut_fstS_sqZeroAut (d : JordanDerivation S (S ⊗[R] A)) :
    mapAut (fstS R S) (sqZeroAut ε eps_mul_eps (mapDer (inlS R S) d)) = 1 := by
  rw [mapAut_sqZeroAut]
  refine jordanAut.ext fun x => ?_
  rw [sqZeroAut_apply, TrivSqZeroExt.fstHom_apply, fst_eps, zero_smul, add_zero,
    jordanAut.one_apply]

section OfDual

variable (g : jordanAut (DualNumber S) (DualNumber S ⊗[R] A)) (hg : mapAut (fstS R S) g = 1)
include hg

/-- An automorphism reducing to the identity is `x ↦ x + ε (ε-component of g(x))` on `S ⊗ A`. -/
theorem apply_tensorMap_inlS (x : S ⊗[R] A) :
    g (tensorMap A (inlS R S) x) = tensorMap A (inlS R S) x +
      (ε : DualNumber S) • tensorMap A (inlS R S) (sndTensor A (g (tensorMap A (inlS R S) x))) := by
  conv_lhs => rw [eq_inl_add_eps_smul (g _)]
  rw [← mapAut_tensorMap, hg, jordanAut.one_apply, tensorMap_fstS_inlS]

/-- The derivation `D` with `g = 1 + ε D`, for `g` reducing to the identity modulo `ε`. -/
noncomputable def derOfDual : JordanDerivation S (S ⊗[R] A) where
  toFun x := sndTensor A (g (tensorMap A (inlS R S) x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' s x := by
    rw [tensorMap_smul, map_smul, sndTensor_inlS_smul, RingHom.id_apply]
  leibniz' x y := by
    change sndTensor A (g (tensorMap A (inlS R S) (x * y))) =
      x * sndTensor A (g (tensorMap A (inlS R S) y)) +
        sndTensor A (g (tensorMap A (inlS R S) x)) * y
    rw [tensorMap_mul, jordanAut.map_mul, apply_tensorMap_inlS g hg x,
      apply_tensorMap_inlS g hg y]
    set dx := sndTensor A (g (tensorMap A (inlS R S) x))
    set dy := sndTensor A (g (tensorMap A (inlS R S) y))
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, eps_mul_eps, dual_zero_smul, add_zero,
      mul_smul_comm, smul_mul_assoc, ← tensorMap_mul, ← tensorMap_mul, ← tensorMap_mul, add_assoc,
      ← dual_smul_add, ← map_add, map_add, sndTensor_tensorMap_inlS, sndTensor_eps_smul, zero_add,
      map_add, map_add, sndTensor_tensorMap_inlS, sndTensor_eps_smul, sndTensor_tensorMap_inlS,
      sndTensor_eps_smul, zero_add, zero_add]

theorem derOfDual_apply (x : S ⊗[R] A) :
    derOfDual g hg x = sndTensor A (g (tensorMap A (inlS R S) x)) := rfl

/-- `g = 1 + ε D` for `D = derOfDual g`. -/
theorem sqZeroAut_derOfDual :
    sqZeroAut ε eps_mul_eps (mapDer (inlS R S) (derOfDual g hg)) = g := by
  refine Subtype.ext (LinearEquiv.toLinearMap_injective (ext_one_tmul fun a => ?_))
  change (1 : DualNumber S) ⊗ₜ a + (ε : DualNumber S) • mapDer (inlS R S) (derOfDual g hg) _ = g _
  rw [mapDer_apply, mapLin_one_tmul, ← tensorMap_one_tmul (inlS R S), apply_tensorMap_inlS g hg]
  rfl

end OfDual

/-- The derivation read off from `1 + ε D` is `D`. -/
theorem derOfDual_sqZeroAut (d : JordanDerivation S (S ⊗[R] A)) :
    derOfDual (sqZeroAut (ε : DualNumber S) eps_mul_eps (mapDer (inlS R S) d))
      (mapAut_fstS_sqZeroAut d) = d := by
  refine JordanDerivation.ext fun x => ?_
  rw [derOfDual_apply, sqZeroAut_apply, mapDer_apply, mapLin_tensorMap, map_add,
    sndTensor_tensorMap_inlS, sndTensor_eps_smul, zero_add]
  rfl

/-- `derOfDual` commutes with scalar-extended homomorphisms intertwining the automorphisms. -/
theorem derOfDual_comm (f : A →ₙₐ[R] B) (g : jordanAut (DualNumber S) (DualNumber S ⊗[R] A))
    (g' : jordanAut (DualNumber S) (DualNumber S ⊗[R] B)) (hg : mapAut (fstS R S) g = 1)
    (hg' : mapAut (fstS R S) g' = 1)
    (h : ∀ z, g' (baseChangeHom (DualNumber S) f z) = baseChangeHom (DualNumber S) f (g z))
    (x : S ⊗[R] A) :
    derOfDual g' hg' (baseChangeHom S f x) = baseChangeHom S f (derOfDual g hg x) := by
  rw [derOfDual_apply, derOfDual_apply, tensorMap_baseChangeHom, h, sndTensor_baseChangeHom]

end JordanAlgebra.BaseChange
