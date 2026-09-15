import Jordan.DivisionAlgebra
import Jordan.Triality.Basic

/-!
# The division algebras of a triality

Choosing nonzero elements in two of the three modules identifies both of those modules with the
(conjugate) dual of the third, and transporting the triality product along these identifications
makes that dual a `DivisionAlgebra R`: a unital non-associative `R`-algebra in which multiplication
by any nonzero element on either side is bijective. (For normed trialities over `ℝ` this is Baez,
*The octonions*, §2.4; here the `bij_*` axioms of `Triality` carry the division-algebra property
directly.)

There is one construction per pair of modules chosen:

| chosen            | common module        | identifications                                  |
|-------------------|----------------------|--------------------------------------------------|
| `e₁ ∈ M1, e₂ ∈ M2` | `DivAlg₁₂ = M3ᵛ`     | `x ↦ t x e₂ ·` (linear), `y ↦ t e₁ y ·` (antilinear) |
| `e₁ ∈ M1, e₃ ∈ M3` | `DivAlg₁₃ = M̄2ᵛ`     | `x ↦ t x · e₃`, `z ↦ t e₁ · z` (both linear)    |
| `e₂ ∈ M2, e₃ ∈ M3` | `DivAlg₂₃ = M1ᵛ`     | `y ↦ t · y e₃` (antilinear), `z ↦ t · e₂ z` (linear) |

In each case the product is `t x y z` with the two chosen-module arguments pulled back along the
identifications, and the unit is `t e e' ·` for the chosen `e, e'`.
-/

namespace Triality

variable {R M1 M2 M3} [CommRing R] [StarRing R]
  [AddCommGroup M1] [Module R M1]
  [AddCommGroup M2] [Module R M2]
  [AddCommGroup M3] [Module R M3]
  (T : Triality R M1 M2 M3)

/-! ## Choosing `e₁ ∈ M1`, `e₂ ∈ M2`: an algebra structure on `M3ᵛ` -/

section DivAlg₁₂

variable {e₁ : M1} {e₂ : M2} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0)

/-- `M3ᵛ`, as a type synonym carrying the algebra structure determined by `e₁, e₂`. -/
def DivAlg₁₂ (_ : Triality R M1 M2 M3) {e₁ : M1} {e₂ : M2} (_he₁ : e₁ ≠ 0) (_he₂ : e₂ ≠ 0) :=
  Module.Dual R M3

namespace DivAlg₁₂

instance : AddCommGroup (T.DivAlg₁₂ he₁ he₂) := inferInstanceAs (AddCommGroup (Module.Dual R M3))
instance : Module R (T.DivAlg₁₂ he₁ he₂) := inferInstanceAs (Module R (Module.Dual R M3))

/-- `M1 ≃ M3ᵛ`, `x ↦ t x e₂ ·`. -/
public noncomputable def ofM1 : M1 ≃ₗ[R] T.DivAlg₁₂ he₁ he₂ := T.yEquiv₁₃ e₂ he₂

/-- `M2 ≃ M3ᵛ` antilinearly, `y ↦ t e₁ y ·`. -/
public noncomputable def ofM2 : M2 ≃ₛₗ[starRingEnd R] T.DivAlg₁₂ he₁ he₂ := T.xEquiv₂₃ e₁ he₁

@[simp] theorem ofM1_apply (x : M1) : ofM1 T he₁ he₂ x = T.triality_prod x e₂ := rfl
@[simp] theorem ofM2_apply (y : M2) : ofM2 T he₁ he₂ y = T.triality_prod e₁ y := rfl

noncomputable instance : Mul (T.DivAlg₁₂ he₁ he₂) where
  mul a b := T.triality_prod ((ofM1 T he₁ he₂).symm a) ((ofM2 T he₁ he₂).symm b)

noncomputable instance : One (T.DivAlg₁₂ he₁ he₂) where
  one := T.triality_prod e₁ e₂

theorem mul_def (a b : T.DivAlg₁₂ he₁ he₂) :
    a * b = T.triality_prod ((ofM1 T he₁ he₂).symm a) ((ofM2 T he₁ he₂).symm b) := rfl

theorem one_def : (1 : T.DivAlg₁₂ he₁ he₂) = T.triality_prod e₁ e₂ := rfl

/-- The product is the triality product transported along the identifications. -/
@[simp] theorem ofM1_mul_ofM2 (x : M1) (y : M2) :
    ofM1 T he₁ he₂ x * ofM2 T he₁ he₂ y = T.triality_prod x y := by
  simp only [mul_def, LinearEquiv.symm_apply_apply]

@[simp] theorem ofM1_symm_one : (ofM1 T he₁ he₂).symm 1 = e₁ :=
  (ofM1 T he₁ he₂).symm_apply_eq.mpr rfl

@[simp] theorem ofM2_symm_one : (ofM2 T he₁ he₂).symm 1 = e₂ :=
  (ofM2 T he₁ he₂).symm_apply_eq.mpr rfl

noncomputable instance : NonAssocRing (T.DivAlg₁₂ he₁ he₂) where
  left_distrib a b c := by simp only [mul_def, map_add]; rfl
  right_distrib a b c := by simp only [mul_def, map_add, LinearMap.add_apply]; rfl
  zero_mul a := by simp only [mul_def, map_zero, LinearMap.zero_apply]; rfl
  mul_zero a := by simp only [mul_def, map_zero]; rfl
  one_mul b := by
    rw [mul_def, ofM1_symm_one]
    exact (ofM2 T he₁ he₂).apply_symm_apply b
  mul_one a := by
    rw [mul_def, ofM2_symm_one]
    exact (ofM1 T he₁ he₂).apply_symm_apply a

instance : IsScalarTower R (T.DivAlg₁₂ he₁ he₂) (T.DivAlg₁₂ he₁ he₂) where
  smul_assoc r a b := by
    simp only [smul_eq_mul, mul_def, map_smul, LinearMap.smul_apply]; rfl

instance : SMulCommClass R (T.DivAlg₁₂ he₁ he₂) (T.DivAlg₁₂ he₁ he₂) where
  smul_comm r a b := by
    simp only [smul_eq_mul, mul_def, map_smulₛₗ, starRingEnd_apply, star_star]; rfl

instance : Nontrivial (T.DivAlg₁₂ he₁ he₂) :=
  nontrivial_of_ne 1 0 fun h => he₂ ((ofM2 T he₁ he₂).map_eq_zero_iff.mp h)

/-- Multiplication by a nonzero element on either side is bijective: transported from
`bij_x_yz` (left) and `bij_y_xz` (right). -/
noncomputable instance : DivisionAlgebra R (T.DivAlg₁₂ he₁ he₂) :=
  DivisionAlgebra.ofBijective
    (fun {a} ha =>
      have hx : (ofM1 T he₁ he₂).symm a ≠ 0 :=
        fun h => ha ((ofM1 T he₁ he₂).symm.map_eq_zero_iff.mp h)
      (T.bij_x_yz _ hx).comp (ofM2 T he₁ he₂).symm.bijective)
    (fun {b} hb =>
      have hy : (ofM2 T he₁ he₂).symm b ≠ 0 :=
        fun h => hb ((ofM2 T he₁ he₂).symm.map_eq_zero_iff.mp h)
      (T.bij_y_xz _ hy).comp (ofM1 T he₁ he₂).symm.bijective)

end DivAlg₁₂

end DivAlg₁₂

/-! ## Choosing `e₁ ∈ M1`, `e₃ ∈ M3`: an algebra structure on `M̄2ᵛ` -/

section DivAlg₁₃

variable {e₁ : M1} {e₃ : M3} (he₁ : e₁ ≠ 0) (he₃ : e₃ ≠ 0)

/-- The conjugate dual `M2 →ₛₗ[starRingEnd R] R`, as a type synonym carrying the algebra
structure determined by `e₁, e₃`. -/
def DivAlg₁₃ (_ : Triality R M1 M2 M3) {e₁ : M1} {e₃ : M3} (_he₁ : e₁ ≠ 0) (_he₃ : e₃ ≠ 0) :=
  M2 →ₛₗ[starRingEnd R] R

namespace DivAlg₁₃

instance : AddCommGroup (T.DivAlg₁₃ he₁ he₃) :=
  inferInstanceAs (AddCommGroup (M2 →ₛₗ[starRingEnd R] R))
instance : Module R (T.DivAlg₁₃ he₁ he₃) := inferInstanceAs (Module R (M2 →ₛₗ[starRingEnd R] R))

/-- `M1 ≃ M̄2ᵛ`, `x ↦ t x · e₃`. -/
public noncomputable def ofM1 : M1 ≃ₗ[R] T.DivAlg₁₃ he₁ he₃ := T.zEquiv₁₂ e₃ he₃

/-- `M3 ≃ M̄2ᵛ`, `z ↦ t e₁ · z`. -/
public noncomputable def ofM3 : M3 ≃ₗ[R] T.DivAlg₁₃ he₁ he₃ := T.xEquiv₃₂ e₁ he₁

@[simp] theorem ofM1_apply (x : M1) : ofM1 T he₁ he₃ x = T.triality_prod_xz x e₃ := rfl
@[simp] theorem ofM3_apply (z : M3) : ofM3 T he₁ he₃ z = T.triality_prod_xz e₁ z := rfl

noncomputable instance : Mul (T.DivAlg₁₃ he₁ he₃) where
  mul a b := T.triality_prod_xz ((ofM1 T he₁ he₃).symm a) ((ofM3 T he₁ he₃).symm b)

noncomputable instance : One (T.DivAlg₁₃ he₁ he₃) where
  one := T.triality_prod_xz e₁ e₃

theorem mul_def (a b : T.DivAlg₁₃ he₁ he₃) :
    a * b = T.triality_prod_xz ((ofM1 T he₁ he₃).symm a) ((ofM3 T he₁ he₃).symm b) := rfl

theorem one_def : (1 : T.DivAlg₁₃ he₁ he₃) = T.triality_prod_xz e₁ e₃ := rfl

/-- The product is the triality product transported along the identifications. -/
@[simp] theorem ofM1_mul_ofM3 (x : M1) (z : M3) :
    ofM1 T he₁ he₃ x * ofM3 T he₁ he₃ z = T.triality_prod_xz x z := by
  simp only [mul_def, LinearEquiv.symm_apply_apply]

@[simp] theorem ofM1_symm_one : (ofM1 T he₁ he₃).symm 1 = e₁ :=
  (ofM1 T he₁ he₃).symm_apply_eq.mpr rfl

@[simp] theorem ofM3_symm_one : (ofM3 T he₁ he₃).symm 1 = e₃ :=
  (ofM3 T he₁ he₃).symm_apply_eq.mpr rfl

noncomputable instance : NonAssocRing (T.DivAlg₁₃ he₁ he₃) where
  left_distrib a b c := by simp only [mul_def, map_add]; rfl
  right_distrib a b c := by simp only [mul_def, map_add, LinearMap.add_apply]; rfl
  zero_mul a := by simp only [mul_def, map_zero, LinearMap.zero_apply]; rfl
  mul_zero a := by simp only [mul_def, map_zero]; rfl
  one_mul b := by
    rw [mul_def, ofM1_symm_one]
    exact (ofM3 T he₁ he₃).apply_symm_apply b
  mul_one a := by
    rw [mul_def, ofM3_symm_one]
    exact (ofM1 T he₁ he₃).apply_symm_apply a

instance : IsScalarTower R (T.DivAlg₁₃ he₁ he₃) (T.DivAlg₁₃ he₁ he₃) where
  smul_assoc r a b := by
    simp only [smul_eq_mul, mul_def, map_smul, LinearMap.smul_apply]; rfl

instance : SMulCommClass R (T.DivAlg₁₃ he₁ he₃) (T.DivAlg₁₃ he₁ he₃) where
  smul_comm r a b := by
    simp only [smul_eq_mul, mul_def, map_smul]; rfl

instance : Nontrivial (T.DivAlg₁₃ he₁ he₃) :=
  nontrivial_of_ne 1 0 fun h => he₃ ((ofM3 T he₁ he₃).map_eq_zero_iff.mp h)

/-- Multiplication by a nonzero element on either side is bijective: transported from
`bij_x_zy` (left) and `bij_z_xy` (right). -/
noncomputable instance : DivisionAlgebra R (T.DivAlg₁₃ he₁ he₃) :=
  DivisionAlgebra.ofBijective
    (fun {a} ha =>
      have hx : (ofM1 T he₁ he₃).symm a ≠ 0 :=
        fun h => ha ((ofM1 T he₁ he₃).symm.map_eq_zero_iff.mp h)
      (T.bij_x_zy _ hx).comp (ofM3 T he₁ he₃).symm.bijective)
    (fun {b} hb =>
      have hz : (ofM3 T he₁ he₃).symm b ≠ 0 :=
        fun h => hb ((ofM3 T he₁ he₃).symm.map_eq_zero_iff.mp h)
      (T.bij_z_xy _ hz).comp (ofM1 T he₁ he₃).symm.bijective)

end DivAlg₁₃

end DivAlg₁₃

/-! ## Choosing `e₂ ∈ M2`, `e₃ ∈ M3`: an algebra structure on `M1ᵛ` -/

section DivAlg₂₃

variable {e₂ : M2} {e₃ : M3} (he₂ : e₂ ≠ 0) (he₃ : e₃ ≠ 0)

/-- `M1ᵛ`, as a type synonym carrying the algebra structure determined by `e₂, e₃`. -/
def DivAlg₂₃ (_ : Triality R M1 M2 M3) {e₂ : M2} {e₃ : M3} (_he₂ : e₂ ≠ 0) (_he₃ : e₃ ≠ 0) :=
  Module.Dual R M1

namespace DivAlg₂₃

instance : AddCommGroup (T.DivAlg₂₃ he₂ he₃) := inferInstanceAs (AddCommGroup (Module.Dual R M1))
instance : Module R (T.DivAlg₂₃ he₂ he₃) := inferInstanceAs (Module R (Module.Dual R M1))

/-- `M2 ≃ M1ᵛ` antilinearly, `y ↦ t · y e₃`. -/
public noncomputable def ofM2 : M2 ≃ₛₗ[starRingEnd R] T.DivAlg₂₃ he₂ he₃ := T.zEquiv₂₁ e₃ he₃

/-- `M3 ≃ M1ᵛ`, `z ↦ t · e₂ z`. -/
public noncomputable def ofM3 : M3 ≃ₗ[R] T.DivAlg₂₃ he₂ he₃ := T.yEquiv₃₁ e₂ he₂

@[simp] theorem ofM2_apply (y : M2) : ofM2 T he₂ he₃ y = T.triality_prod_yz y e₃ := rfl
@[simp] theorem ofM3_apply (z : M3) : ofM3 T he₂ he₃ z = T.triality_prod_yz e₂ z := rfl

noncomputable instance : Mul (T.DivAlg₂₃ he₂ he₃) where
  mul a b := T.triality_prod_yz ((ofM2 T he₂ he₃).symm a) ((ofM3 T he₂ he₃).symm b)

noncomputable instance : One (T.DivAlg₂₃ he₂ he₃) where
  one := T.triality_prod_yz e₂ e₃

theorem mul_def (a b : T.DivAlg₂₃ he₂ he₃) :
    a * b = T.triality_prod_yz ((ofM2 T he₂ he₃).symm a) ((ofM3 T he₂ he₃).symm b) := rfl

theorem one_def : (1 : T.DivAlg₂₃ he₂ he₃) = T.triality_prod_yz e₂ e₃ := rfl

/-- The product is the triality product transported along the identifications. -/
@[simp] theorem ofM2_mul_ofM3 (y : M2) (z : M3) :
    ofM2 T he₂ he₃ y * ofM3 T he₂ he₃ z = T.triality_prod_yz y z := by
  simp only [mul_def, LinearEquiv.symm_apply_apply]

@[simp] theorem ofM2_symm_one : (ofM2 T he₂ he₃).symm 1 = e₂ :=
  (ofM2 T he₂ he₃).symm_apply_eq.mpr rfl

@[simp] theorem ofM3_symm_one : (ofM3 T he₂ he₃).symm 1 = e₃ :=
  (ofM3 T he₂ he₃).symm_apply_eq.mpr rfl

noncomputable instance : NonAssocRing (T.DivAlg₂₃ he₂ he₃) where
  left_distrib a b c := by simp only [mul_def, map_add]; rfl
  right_distrib a b c := by simp only [mul_def, map_add, LinearMap.add_apply]; rfl
  zero_mul a := by simp only [mul_def, map_zero, LinearMap.zero_apply]; rfl
  mul_zero a := by simp only [mul_def, map_zero]; rfl
  one_mul b := by
    rw [mul_def, ofM2_symm_one]
    exact (ofM3 T he₂ he₃).apply_symm_apply b
  mul_one a := by
    rw [mul_def, ofM3_symm_one]
    exact (ofM2 T he₂ he₃).apply_symm_apply a

instance : IsScalarTower R (T.DivAlg₂₃ he₂ he₃) (T.DivAlg₂₃ he₂ he₃) where
  smul_assoc r a b := by
    simp only [smul_eq_mul, mul_def, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply,
      star_star]; rfl

instance : SMulCommClass R (T.DivAlg₂₃ he₂ he₃) (T.DivAlg₂₃ he₂ he₃) where
  smul_comm r a b := by
    simp only [smul_eq_mul, mul_def, map_smul]; rfl

instance : Nontrivial (T.DivAlg₂₃ he₂ he₃) :=
  nontrivial_of_ne 1 0 fun h => he₃ ((ofM3 T he₂ he₃).map_eq_zero_iff.mp h)

/-- Multiplication by a nonzero element on either side is bijective: transported from
`bij_y_zx` (left) and `bij_z_yx` (right). -/
noncomputable instance : DivisionAlgebra R (T.DivAlg₂₃ he₂ he₃) :=
  DivisionAlgebra.ofBijective
    (fun {a} ha =>
      have hy : (ofM2 T he₂ he₃).symm a ≠ 0 :=
        fun h => ha ((ofM2 T he₂ he₃).symm.map_eq_zero_iff.mp h)
      (T.bij_y_zx _ hy).comp (ofM3 T he₂ he₃).symm.bijective)
    (fun {b} hb =>
      have hz : (ofM3 T he₂ he₃).symm b ≠ 0 :=
        fun h => hb ((ofM3 T he₂ he₃).symm.map_eq_zero_iff.mp h)
      (T.bij_z_yx _ hz).comp (ofM2 T he₂ he₃).symm.bijective)

end DivAlg₂₃

end DivAlg₂₃

end Triality
