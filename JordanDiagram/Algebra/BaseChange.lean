import JordanDiagram.Algebra.Automorphism
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Scalar extension of Jordan algebras (Lemma 2.4)

For a commutative `R`-algebra `S` and a Jordan `R`-algebra `A`, with `2` invertible in `R`, the
`S`-algebra `S ⊗[R] A` is a Jordan algebra (`instJordanAlgebra`).

The proof is the paper's. With `2` invertible the fully linearized Jordan identity
`lin a b c y = [L_a, L_{bc}] y + [L_b, L_{ca}] y + [L_c, L_{ab}] y = 0` holds in `A`
(`JordanAlgebra.lie_lmul_lmul_add_add_eq_zero`). It is `R`-multilinear, so it holds in `S ⊗ A`
because it holds on pure tensors. The Jordan expression `jordanExpr x y = [L_x, L_{x²}] y` is cubic
in `x`, and `jordanExpr (x + z) = jordanExpr x + jordanExpr z + lin x x z + lin z z x`
(`jordanExpr_add`), so it vanishes on sums of pure tensors.

Scalar extension is functorial (`baseChangeHom`), and transports automorphisms and derivations
(`baseChangeAut`, `baseChangeDer`).
-/

open TensorProduct

namespace JordanAlgebra

section Generic

variable {M : Type*} [NonUnitalNonAssocRing M]

/-- The fully linearized Jordan expression `[L_a, L_{bc}] y + [L_b, L_{ca}] y + [L_c, L_{ab}] y`. -/
def lin (a b c y : M) : M :=
  a * ((b * c) * y) - (b * c) * (a * y) + (b * ((c * a) * y) - (c * a) * (b * y)) +
    (c * ((a * b) * y) - (a * b) * (c * y))

/-- The Jordan expression `[L_x, L_{x²}] y`; the Jordan identity says it vanishes. -/
def jordanExpr (x y : M) : M := x * ((x * x) * y) - (x * x) * (x * y)

theorem lin_add₁ (a a' b c y : M) : lin (a + a') b c y = lin a b c y + lin a' b c y := by
  simp only [lin, mul_add, add_mul]; abel

theorem lin_add₂ (a b b' c y : M) : lin a (b + b') c y = lin a b c y + lin a b' c y := by
  simp only [lin, mul_add, add_mul]; abel

theorem lin_add₃ (a b c c' y : M) : lin a b (c + c') y = lin a b c y + lin a b c' y := by
  simp only [lin, mul_add, add_mul]; abel

theorem lin_add₄ (a b c y y' : M) : lin a b c (y + y') = lin a b c y + lin a b c y' := by
  simp only [lin, mul_add]; abel

theorem lin_zero₁ (b c y : M) : lin 0 b c y = 0 := by simp [lin]
theorem lin_zero₂ (a c y : M) : lin a 0 c y = 0 := by simp [lin]
theorem lin_zero₃ (a b y : M) : lin a b 0 y = 0 := by simp [lin]
theorem lin_zero₄ (a b c : M) : lin a b c 0 = 0 := by simp [lin]

theorem jordanExpr_add₂ (x y y' : M) : jordanExpr x (y + y') = jordanExpr x y + jordanExpr x y' := by
  simp only [jordanExpr, mul_add]; abel

/-- The cubic Jordan expression is additive up to the linearized cross terms. -/
theorem jordanExpr_add (hcomm : ∀ a b : M, a * b = b * a) (x z y : M) :
    jordanExpr (x + z) y = jordanExpr x y + jordanExpr z y + lin x x z y + lin z z x y := by
  simp only [jordanExpr, lin, mul_add, add_mul, hcomm z x]
  abel

end Generic

variable {R : Type*} [CommRing R] {A : Type*} [JordanAlgebra R A]

attribute [local instance] LieRing.ofAssociativeRing in
/-- The fully linearized Jordan identity in a Jordan algebra with `2` invertible. -/
theorem lin_eq_zero [Invertible (2 : R)] (a b c y : A) : lin a b c y = 0 := by
  have h := congrArg (fun f : AddMonoid.End A => f y) (lie_lmul_lmul_add_add_eq_zero (R := R) a b c)
  simp only [Ring.lie_def] at h
  exact h

theorem jordanExpr_eq_zero (x y : A) : jordanExpr x y = 0 := by
  rw [jordanExpr, sub_eq_zero]
  exact (jordan_identity x y).symm

namespace BaseChange

variable (S : Type*) [CommRing S] [Algebra R S]

theorem mul_comm' (x y : S ⊗[R] A) : x * y = y * x := by
  induction x with
  | tmul s a =>
    induction y with
    | tmul t b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s t,
        jordan_mul_comm a b]
    | add y z hy hz => rw [mul_add, add_mul, hy, hz]
  | add x z hx hz => rw [add_mul, mul_add, hx, hz]

theorem lin_tmul (s t u v : S) (a b c y : A) :
    lin (s ⊗ₜ[R] a) (t ⊗ₜ b) (u ⊗ₜ c) (v ⊗ₜ y) = (s * t * u * v) ⊗ₜ lin a b c y := by
  simp only [lin, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub,
    TensorProduct.tmul_add]
  simp only [mul_comm, mul_left_comm]

theorem lin_eq_zero [Invertible (2 : R)] (a b c y : S ⊗[R] A) : lin a b c y = 0 := by
  induction a with
  | add a a' ha ha' => rw [lin_add₁, ha, ha', add_zero]
  | tmul s a =>
    induction b with
    | add b b' hb hb' => rw [lin_add₂, hb, hb', add_zero]
    | tmul t b =>
      induction c with
      | add c c' hc hc' => rw [lin_add₃, hc, hc', add_zero]
      | tmul u c =>
        induction y with
        | add y y' hy hy' => rw [lin_add₄, hy, hy', add_zero]
        | tmul v y => rw [lin_tmul, JordanAlgebra.lin_eq_zero (R := R), TensorProduct.tmul_zero]

theorem jordanExpr_eq_zero [Invertible (2 : R)] (x y : S ⊗[R] A) : jordanExpr x y = 0 := by
  induction x with
  | add x z hx hz =>
    rw [jordanExpr_add (mul_comm' S), hx, hz, lin_eq_zero, lin_eq_zero]
    simp
  | tmul s a =>
    induction y with
    | add y y' hy hy' => rw [jordanExpr_add₂, hy, hy', add_zero]
    | tmul t b =>
      have h : jordanExpr (s ⊗ₜ[R] a) (t ⊗ₜ b) = (s * s * s * t) ⊗ₜ jordanExpr a b := by
        simp only [jordanExpr, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
        simp only [mul_comm, mul_left_comm]
      rw [h, JordanAlgebra.jordanExpr_eq_zero, TensorProduct.tmul_zero]

variable [Invertible (2 : R)]

/-- **Lemma 2.4** (scalar extension): with `2` invertible in `R`, `S ⊗[R] A` is a Jordan
`S`-algebra for every commutative `R`-algebra `S`. -/
instance instJordanAlgebra : JordanAlgebra S (S ⊗[R] A) :=
  { (inferInstance : NonAssocRing (S ⊗[R] A)), (inferInstance : Module S (S ⊗[R] A)),
    (inferInstance : IsScalarTower S (S ⊗[R] A) (S ⊗[R] A)),
    (inferInstance : SMulCommClass S (S ⊗[R] A) (S ⊗[R] A)) with
    jordan_mul_comm := mul_comm' S
    jordan_identity := fun x y => by
      have h := jordanExpr_eq_zero S x y
      rw [jordanExpr, sub_eq_zero] at h
      exact h.symm }

variable {S}
variable {B : Type*} [JordanAlgebra R B]

omit [Invertible (2 : R)] in
theorem baseChange_mul (f : A →ₙₐ[R] B) (x y : S ⊗[R] A) :
    (toLin f).baseChange S (x * y) = (toLin f).baseChange S x * (toLin f).baseChange S y := by
  induction x with
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]
  | tmul s a =>
    induction y with
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | tmul t b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul, toLin_apply,
        _root_.map_mul]

variable (S) in
/-- Scalar extension of a morphism of `Jord_R` (functoriality in Lemma 2.4). -/
noncomputable def baseChangeHom (f : A →ₙₐ[R] B) : S ⊗[R] A →ₙₐ[S] S ⊗[R] B where
  toFun := (toLin f).baseChange S
  map_smul' := ((toLin f).baseChange S).map_smul
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := baseChange_mul f

omit [Invertible (2 : R)] in
@[simp]
theorem baseChangeHom_tmul (f : A →ₙₐ[R] B) (s : S) (a : A) :
    baseChangeHom S f (s ⊗ₜ a) = s ⊗ₜ f a := rfl

omit [Invertible (2 : R)] in
theorem baseChangeHom_injective_of_flat [Module.Flat R S] (f : A →ₙₐ[R] B)
    (hf : Function.Injective f) : Function.Injective (baseChangeHom S f) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := S) (toLin f) hf

variable (S) in
/-- Scalar extension of Jordan automorphisms, a group homomorphism
`Aut_{Jord_R}(A) → Aut_{Jord_S}(S ⊗ A)`. -/
noncomputable def baseChangeAut : jordanAut R A →* jordanAut S (S ⊗[R] A) where
  toFun g := ⟨(g : A ≃ₗ[R] A).baseChange R S A A, by
    intro x y
    exact baseChange_mul (jordanAut.toHom g) x y⟩
  map_one' := Subtype.ext (LinearEquiv.baseChange_one R S A)
  map_mul' g h := Subtype.ext (LinearEquiv.baseChange_mul R S A g h)

@[simp]
theorem baseChangeAut_tmul (g : jordanAut R A) (s : S) (a : A) :
    baseChangeAut S g (s ⊗ₜ a) = s ⊗ₜ g a := rfl

variable (S) in
/-- Scalar extension of a Jordan derivation. -/
noncomputable def baseChangeDer (d : JordanDerivation R A) : JordanDerivation S (S ⊗[R] A) where
  toLinearMap := (d : A →ₗ[R] A).baseChange S
  leibniz' x y := by
    induction x with
    | add x z hx hz => simp only [add_mul, map_add, hx, hz]; abel
    | tmul s a =>
      induction y with
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]; abel
      | tmul t b =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          JordanDerivation.coeFn_coe, JordanDerivation.leibniz, TensorProduct.tmul_add]

@[simp]
theorem baseChangeDer_tmul (d : JordanDerivation R A) (s : S) (a : A) :
    baseChangeDer S d (s ⊗ₜ a) = s ⊗ₜ d a := rfl

theorem baseChangeDer_add (d e : JordanDerivation R A) :
    baseChangeDer S (d + e) = baseChangeDer S d + baseChangeDer S e := by
  refine JordanDerivation.ext fun x => ?_
  induction x with
  | add x y hx hy =>
    rw [JordanDerivation.map_add, hx, hy, JordanDerivation.map_add]
  | tmul s a =>
    change s ⊗ₜ (d a + e a) = s ⊗ₜ d a + s ⊗ₜ e a
    rw [TensorProduct.tmul_add]

theorem baseChangeDer_lie (d e : JordanDerivation R A) :
    baseChangeDer S ⁅d, e⁆ = ⁅baseChangeDer S d, baseChangeDer S e⁆ := by
  refine JordanDerivation.ext fun x => ?_
  induction x with
  | add x y hx hy =>
    rw [JordanDerivation.map_add, hx, hy, JordanDerivation.map_add]
  | tmul s a =>
    change s ⊗ₜ (d (e a) - e (d a)) = s ⊗ₜ d (e a) - s ⊗ₜ e (d a)
    rw [TensorProduct.tmul_sub]

/-- Scalar extension preserves the commutation `g' ∘ f = f ∘ g` of automorphisms with a
morphism. -/
theorem baseChangeAut_comm {g : jordanAut R A} {g' : jordanAut R B} {f : A →ₙₐ[R] B}
    (h : ∀ a, g' (f a) = f (g a)) (x : S ⊗[R] A) :
    baseChangeAut S g' (baseChangeHom S f x) = baseChangeHom S f (baseChangeAut S g x) := by
  induction x with
  | add x y hx hy =>
    change ((baseChangeAut S g' : jordanAut S (S ⊗[R] B)) : S ⊗[R] B ≃ₗ[S] S ⊗[R] B)
        (baseChangeHom S f (x + y)) =
      baseChangeHom S f (((baseChangeAut S g : jordanAut S (S ⊗[R] A)) :
        S ⊗[R] A ≃ₗ[S] S ⊗[R] A) (x + y))
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul s a =>
    change s ⊗ₜ g' (f a) = s ⊗ₜ f (g a)
    rw [h]

/-- Scalar extension preserves the commutation `d' ∘ f = f ∘ d` of derivations with a
morphism. -/
theorem baseChangeDer_comm {d : JordanDerivation R A} {d' : JordanDerivation R B}
    {f : A →ₙₐ[R] B} (h : ∀ a, d' (f a) = f (d a)) (x : S ⊗[R] A) :
    baseChangeDer S d' (baseChangeHom S f x) = baseChangeHom S f (baseChangeDer S d x) := by
  induction x with
  | add x y hx hy =>
    rw [map_add, JordanDerivation.map_add, hx, hy, JordanDerivation.map_add, map_add]
  | tmul s a =>
    change s ⊗ₜ d' (f a) = s ⊗ₜ f (d a)
    rw [h]

section Descent

/-! ### Descent of automorphisms (input to Proposition 7.9(c))

An `E`-automorphism `g` of `E ⊗[R] A` that preserves `1 ⊗ A` (as does its inverse) restricts,
along the injective map `incl : a ↦ 1 ⊗ a`, to an `R`-automorphism `h` of `A`, and
`id_E ⊗ h = g` because `1 ⊗ A` spans `E ⊗ A` over `E`. -/

variable {E : Type*} [CommRing E] [Algebra R E]

variable (E) in
/-- The map `A → E ⊗[R] A`, `a ↦ 1 ⊗ a`. -/
def incl (a : A) : E ⊗[R] A := (1 : E) ⊗ₜ a

omit [Invertible (2 : R)] in
theorem incl_add (a b : A) : incl E (a + b) = incl E a + incl E b := TensorProduct.tmul_add _ _ _

omit [Invertible (2 : R)] in
theorem incl_smul (r : R) (a : A) : incl E (r • a) = r • incl E a := TensorProduct.tmul_smul _ _ _

omit [Invertible (2 : R)] in
theorem incl_mul (a b : A) : incl E (a * b) = incl E a * incl E b := by
  simp only [incl, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

@[simp]
theorem baseChangeAut_incl (h : jordanAut R A) (a : A) :
    baseChangeAut E h (incl E a) = incl E (h a) := rfl

theorem jordanAut_map_add (g : jordanAut E (E ⊗[R] A)) (x y : E ⊗[R] A) :
    g (x + y) = g x + g y :=
  (g : E ⊗[R] A ≃ₗ[E] E ⊗[R] A).map_add x y

theorem jordanAut_map_smul_of_tower (g : jordanAut E (E ⊗[R] A)) (r : R) (x : E ⊗[R] A) :
    g (r • x) = r • g x := by
  rw [← algebraMap_smul E r x, ← algebraMap_smul E r (g x)]
  exact (g : E ⊗[R] A ≃ₗ[E] E ⊗[R] A).map_smul _ _

variable (hι : Function.Injective (incl (A := A) E))

/-- `g` maps `1 ⊗ A` into itself. -/
def PreservesIncl (g : jordanAut E (E ⊗[R] A)) : Prop := ∀ a, ∃ b, g (incl E a) = incl E b

/-- The restriction of `g` to `A`, as a function. -/
noncomputable def descendFun (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g) (a : A) : A :=
  (hg a).choose

theorem incl_descendFun (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g) (a : A) :
    incl E (descendFun g hg a) = g (incl E a) :=
  ((hg a).choose_spec).symm

/-- The restriction of `g` to `A`, as a linear map. -/
noncomputable def descendLin (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g) : A →ₗ[R] A where
  toFun := descendFun g hg
  map_add' a b := hι <| calc
    incl E (descendFun g hg (a + b)) = g (incl E a + incl E b) := by
      rw [incl_descendFun, incl_add]
    _ = incl E (descendFun g hg a + descendFun g hg b) := by
      rw [jordanAut_map_add, incl_add, incl_descendFun, incl_descendFun]
  map_smul' r a := hι <| calc
    incl E (descendFun g hg (r • a)) = g (r • incl E a) := by
      rw [incl_descendFun, incl_smul]
    _ = incl E (r • descendFun g hg a) := by
      rw [jordanAut_map_smul_of_tower, incl_smul, incl_descendFun]

theorem incl_descendLin (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g) (a : A) :
    incl E (descendLin hι g hg a) = g (incl E a) :=
  incl_descendFun g hg a

theorem descendLin_mul (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g) (a b : A) :
    descendLin hι g hg (a * b) = descendLin hι g hg a * descendLin hι g hg b :=
  hι <| by rw [incl_mul, incl_descendLin, incl_descendLin, incl_descendLin, incl_mul,
    jordanAut.map_mul]

theorem descendLin_inv (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g)
    (hg' : PreservesIncl g⁻¹) (a : A) :
    descendLin hι g hg (descendLin hι g⁻¹ hg' a) = a :=
  hι <| by rw [incl_descendLin, incl_descendLin, jordanAut.apply_inv_self]

/-- **Descent**: an automorphism of `E ⊗[R] A` preserving `1 ⊗ A` together with its inverse
comes from an automorphism of `A`. -/
noncomputable def descendAut (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g)
    (hg' : PreservesIncl g⁻¹) : jordanAut R A :=
  ⟨LinearEquiv.ofLinear (descendLin hι g hg) (descendLin hι g⁻¹ hg')
      (LinearMap.ext fun a => descendLin_inv hι g hg hg' a)
      (LinearMap.ext fun a => by
        have := descendLin_inv hι g⁻¹ hg' (by simpa using hg) a
        simpa using this),
    descendLin_mul hι g hg⟩

theorem incl_descendAut (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g)
    (hg' : PreservesIncl g⁻¹) (a : A) :
    incl E (descendAut hι g hg hg' a) = g (incl E a) :=
  incl_descendLin hι g hg a

theorem baseChangeAut_descendAut (g : jordanAut E (E ⊗[R] A)) (hg : PreservesIncl g)
    (hg' : PreservesIncl g⁻¹) : baseChangeAut E (descendAut hι g hg hg') = g := by
  refine jordanAut.ext fun x => ?_
  induction x with
  | add x y hx hy =>
    change ((baseChangeAut E _ : jordanAut E (E ⊗[R] A)) : E ⊗[R] A ≃ₗ[E] E ⊗[R] A) (x + y) =
      g (x + y)
    rw [map_add, jordanAut_map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul s a =>
    have hs : s ⊗ₜ[R] a = s • incl E a := by
      rw [incl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs]
    change ((baseChangeAut E _ : jordanAut E (E ⊗[R] A)) : E ⊗[R] A ≃ₗ[E] E ⊗[R] A)
        (s • incl E a) = ((g : jordanAut E (E ⊗[R] A)) : E ⊗[R] A ≃ₗ[E] E ⊗[R] A) (s • incl E a)
    rw [map_smul, map_smul]
    exact congrArg (s • ·) (incl_descendAut hι g hg hg' a)

end Descent

end BaseChange

end JordanAlgebra
