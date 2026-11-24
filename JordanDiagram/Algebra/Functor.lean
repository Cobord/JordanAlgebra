import JordanDiagram.Algebra.BaseChange

/-!
# Transport of automorphisms along algebra maps (functoriality of Proposition 3.3)

For commutative `R`-algebras `S`, `T` and `φ : S →ₐ[R] T`, write `φ ⊗ 1 : S ⊗[R] A → T ⊗[R] A`
(`tensorMap φ`). An `S`-linear endomorphism `f` of `S ⊗[R] A` transports to the `T`-linear
endomorphism `mapLin φ f`, `t ⊗ a ↦ t • (φ ⊗ 1)(f (1 ⊗ a))`. It is the unique `T`-linear map with
`mapLin φ f ∘ (φ ⊗ 1) = (φ ⊗ 1) ∘ f` (`mapLin_tensorMap`, `ext_one_tmul`), which is what makes the
functor laws work:

* `mapLin_comp`, `mapLin_id`: transport preserves composition and the identity;
* `mapLin_id_alg`, `mapLin_comp_alg`: transport along `id` is the identity, and transport along
  `χ ∘ φ` is transport along `φ` followed by transport along `χ`;
* `mapLin_baseChange`: transport extends scalar extension from `R`.

`mapAut φ : Aut(S ⊗ A) →* Aut(T ⊗ A)` is the resulting group homomorphism. This gives the functor
`S ↦ Aut_{Jord_S}(S ⊗[R] A)` on commutative `R`-algebras, which `JordanDiagram.autFunctor`
extends to diagrams.
-/

open TensorProduct

namespace JordanAlgebra.BaseChange

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {A : Type*} [JordanAlgebra R A] {B : Type*} [JordanAlgebra R B]
variable {S : Type*} [CommRing S] [Algebra R S]
variable {T : Type*} [CommRing T] [Algebra R T]
variable {U : Type*} [CommRing U] [Algebra R U]

section TensorMap

variable (A) in
/-- `φ ⊗ 1 : S ⊗[R] A → T ⊗[R] A`. -/
noncomputable def tensorMap (φ : S →ₐ[R] T) : S ⊗[R] A →ₗ[R] T ⊗[R] A :=
  TensorProduct.map φ.toLinearMap LinearMap.id

omit [Invertible (2 : R)] in
@[simp]
theorem tensorMap_tmul (φ : S →ₐ[R] T) (s : S) (a : A) : tensorMap A φ (s ⊗ₜ a) = φ s ⊗ₜ a := rfl

omit [Invertible (2 : R)] in
theorem tensorMap_smul (φ : S →ₐ[R] T) (s : S) (x : S ⊗[R] A) :
    tensorMap A φ (s • x) = φ s • tensorMap A φ x := by
  induction x with
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul s' a =>
    rw [TensorProduct.smul_tmul', tensorMap_tmul, tensorMap_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]

omit [Invertible (2 : R)] in
theorem tensorMap_mul (φ : S →ₐ[R] T) (x y : S ⊗[R] A) :
    tensorMap A φ (x * y) = tensorMap A φ x * tensorMap A φ y := by
  induction x with
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]
  | tmul s a =>
    induction y with
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | tmul t b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorMap_tmul, map_mul]

omit [Invertible (2 : R)] in
theorem tensorMap_id (x : S ⊗[R] A) : tensorMap A (AlgHom.id R S) x = x := by
  induction x with
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul s a => rfl

omit [Invertible (2 : R)] in
theorem tensorMap_comp (φ : S →ₐ[R] T) (χ : T →ₐ[R] U) (x : S ⊗[R] A) :
    tensorMap A (χ.comp φ) x = tensorMap A χ (tensorMap A φ x) := by
  induction x with
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | tmul s a => rfl

omit [Invertible (2 : R)] in
theorem tensorMap_baseChangeHom (φ : S →ₐ[R] T) (f : A →ₙₐ[R] B) (x : S ⊗[R] A) :
    tensorMap B φ (baseChangeHom S f x) = baseChangeHom T f (tensorMap A φ x) := by
  induction x with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s a => rfl

end TensorMap

section Ext

omit [Invertible (2 : R)] in
/-- `T`-linear maps out of `T ⊗[R] A` are determined on the elements `1 ⊗ a`. -/
theorem ext_one_tmul {P : Type*} [AddCommGroup P] [Module T P] [Module R P] [IsScalarTower R T P]
    {f g : T ⊗[R] A →ₗ[T] P} (h : ∀ a, f ((1 : T) ⊗ₜ a) = g ((1 : T) ⊗ₜ a)) : f = g := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro t a
  have e : t ⊗ₜ[R] a = t • ((1 : T) ⊗ₜ[R] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, map_smul, h]

end Ext

section MapLin

variable (φ : S →ₐ[R] T)

/-- Transport of an `S`-linear endomorphism of `S ⊗[R] A` along `φ : S →ₐ[R] T`. -/
noncomputable def mapLin (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) : T ⊗[R] A →ₗ[T] T ⊗[R] A :=
  LinearMap.liftBaseChange T
    (tensorMap A φ ∘ₗ f.restrictScalars R ∘ₗ TensorProduct.mk R S A 1)

omit [Invertible (2 : R)] in
@[simp]
theorem mapLin_tmul (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) (t : T) (a : A) :
    mapLin φ f (t ⊗ₜ a) = t • tensorMap A φ (f ((1 : S) ⊗ₜ a)) := rfl

omit [Invertible (2 : R)] in
theorem mapLin_one_tmul (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) (a : A) :
    mapLin φ f ((1 : T) ⊗ₜ a) = tensorMap A φ (f ((1 : S) ⊗ₜ a)) := by
  rw [mapLin_tmul, one_smul]

omit [Invertible (2 : R)] in
/-- The defining property: `mapLin φ f ∘ (φ ⊗ 1) = (φ ⊗ 1) ∘ f`. -/
theorem mapLin_tensorMap (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) (x : S ⊗[R] A) :
    mapLin φ f (tensorMap A φ x) = tensorMap A φ (f x) := by
  induction x with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s a =>
    have e : s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [tensorMap_tmul, mapLin_tmul, e, map_smul, tensorMap_smul]

omit [Invertible (2 : R)] in
theorem tensorMap_one_tmul (a : A) : tensorMap A φ ((1 : S) ⊗ₜ a) = (1 : T) ⊗ₜ a := by
  rw [tensorMap_tmul, map_one]

omit [Invertible (2 : R)] in
theorem mapLin_comp (f g : S ⊗[R] A →ₗ[S] S ⊗[R] A) :
    mapLin φ (f ∘ₗ g) = mapLin φ f ∘ₗ mapLin φ g := by
  refine ext_one_tmul fun a => ?_
  rw [LinearMap.comp_apply, mapLin_one_tmul, mapLin_one_tmul, mapLin_tensorMap,
    LinearMap.comp_apply]

omit [Invertible (2 : R)] in
theorem mapLin_id : mapLin φ (LinearMap.id : S ⊗[R] A →ₗ[S] S ⊗[R] A) = LinearMap.id := by
  refine ext_one_tmul fun a => ?_
  rw [mapLin_one_tmul, LinearMap.id_apply, LinearMap.id_apply, tensorMap_one_tmul]

omit [Invertible (2 : R)] in
theorem mapLin_id_alg (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) : mapLin (AlgHom.id R S) f = f := by
  refine ext_one_tmul fun a => ?_
  rw [mapLin_one_tmul, tensorMap_id]

omit [Invertible (2 : R)] in
theorem mapLin_comp_alg (χ : T →ₐ[R] U) (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) :
    mapLin (χ.comp φ) f = mapLin χ (mapLin φ f) := by
  refine ext_one_tmul fun a => ?_
  rw [mapLin_one_tmul, mapLin_one_tmul, ← tensorMap_one_tmul φ, mapLin_tensorMap, tensorMap_comp]

omit [Invertible (2 : R)] in
theorem mapLin_baseChange (h : A →ₗ[R] A) :
    mapLin φ (h.baseChange S) = h.baseChange T := by
  refine ext_one_tmul fun a => ?_
  rw [mapLin_one_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, tensorMap_one_tmul]

omit [Invertible (2 : R)] in
theorem mapLin_mul (f : S ⊗[R] A →ₗ[S] S ⊗[R] A) (hf : ∀ x y, f (x * y) = f x * f y)
    (x y : T ⊗[R] A) : mapLin φ f (x * y) = mapLin φ f x * mapLin φ f y := by
  induction x with
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]
  | tmul t a =>
    induction y with
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | tmul t' b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mapLin_tmul, mapLin_tmul, mapLin_tmul,
        smul_mul_smul_comm]
      congr 1
      rw [← tensorMap_mul, ← hf, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

omit [Invertible (2 : R)] in
/-- The commutation of transported maps with the scalar extension of a morphism. -/
theorem mapLin_baseChangeHom_comm (f : A →ₙₐ[R] B) (g : S ⊗[R] A →ₗ[S] S ⊗[R] A)
    (g' : S ⊗[R] B →ₗ[S] S ⊗[R] B)
    (h : ∀ x, g' (baseChangeHom S f x) = baseChangeHom S f (g x)) (x : T ⊗[R] A) :
    mapLin φ g' (baseChangeHom T f x) = baseChangeHom T f (mapLin φ g x) := by
  have key : (mapLin φ g').comp ((toLin f).baseChange T) =
      ((toLin f).baseChange T).comp (mapLin φ g) := by
    refine ext_one_tmul fun a => ?_
    change mapLin φ g' (baseChangeHom T f ((1 : T) ⊗ₜ a)) =
      baseChangeHom T f (mapLin φ g ((1 : T) ⊗ₜ a))
    rw [mapLin_one_tmul, ← tensorMap_one_tmul φ (A := A), ← tensorMap_baseChangeHom,
      mapLin_tensorMap, h, tensorMap_baseChangeHom]
  exact LinearMap.congr_fun key x

end MapLin

section MapAut

variable (φ : S →ₐ[R] T)

/-- Transport of Jordan automorphisms along `φ : S →ₐ[R] T`, a group homomorphism
`Aut_{Jord_S}(S ⊗[R] A) → Aut_{Jord_T}(T ⊗[R] A)` (Proposition 3.3). -/
noncomputable def mapAut : jordanAut S (S ⊗[R] A) →* jordanAut T (T ⊗[R] A) where
  toFun g := ⟨LinearEquiv.ofLinearMap (mapLin φ (g : S ⊗[R] A ≃ₗ[S] S ⊗[R] A).toLinearMap)
      (mapLin φ ((g⁻¹ : jordanAut S (S ⊗[R] A)) : S ⊗[R] A ≃ₗ[S] S ⊗[R] A).toLinearMap)
      (by
        rw [← mapLin_comp, ← mapLin_id φ]
        congr 1
        exact LinearMap.ext fun x => jordanAut.apply_inv_self g x)
      (by
        rw [← mapLin_comp, ← mapLin_id φ]
        congr 1
        exact LinearMap.ext fun x => jordanAut.inv_apply_self g x),
    mapLin_mul φ _ (jordanAut.map_mul g)⟩
  map_one' := Subtype.ext (LinearEquiv.toLinearMap_injective (mapLin_id φ))
  map_mul' g h := Subtype.ext (LinearEquiv.toLinearMap_injective (mapLin_comp φ _ _))

theorem mapAut_apply (g : jordanAut S (S ⊗[R] A)) (x : T ⊗[R] A) :
    mapAut φ g x = mapLin φ (g : S ⊗[R] A ≃ₗ[S] S ⊗[R] A).toLinearMap x := rfl

theorem mapAut_id_alg (g : jordanAut S (S ⊗[R] A)) : mapAut (AlgHom.id R S) g = g :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (mapLin_id_alg _))

theorem mapAut_comp_alg (χ : T →ₐ[R] U) (g : jordanAut S (S ⊗[R] A)) :
    mapAut (χ.comp φ) g = mapAut χ (mapAut φ g) :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (mapLin_comp_alg φ χ _))

/-- Transport along `φ` extends scalar extension from `R`. -/
theorem mapAut_baseChangeAut (h : jordanAut R A) :
    mapAut φ (baseChangeAut S h) = baseChangeAut T h :=
  Subtype.ext (LinearEquiv.toLinearMap_injective (mapLin_baseChange φ _))

end MapAut

section MapDer

variable (φ : S →ₐ[R] T)

omit [Invertible (2 : R)] in
theorem mapLin_add (f g : S ⊗[R] A →ₗ[S] S ⊗[R] A) :
    mapLin φ (f + g) = mapLin φ f + mapLin φ g := by
  refine ext_one_tmul fun a => ?_
  rw [LinearMap.add_apply, mapLin_one_tmul, mapLin_one_tmul, mapLin_one_tmul,
    LinearMap.add_apply, map_add]

omit [Invertible (2 : R)] in
theorem mapLin_sub (f g : S ⊗[R] A →ₗ[S] S ⊗[R] A) :
    mapLin φ (f - g) = mapLin φ f - mapLin φ g := by
  refine ext_one_tmul fun a => ?_
  rw [LinearMap.sub_apply, mapLin_one_tmul, mapLin_one_tmul, mapLin_one_tmul,
    LinearMap.sub_apply, map_sub]

/-- Transport of a Jordan derivation of `S ⊗[R] A` along `φ : S →ₐ[R] T`. -/
noncomputable def mapDer (d : JordanDerivation S (S ⊗[R] A)) : JordanDerivation T (T ⊗[R] A) where
  toLinearMap := mapLin φ (d : S ⊗[R] A →ₗ[S] S ⊗[R] A)
  leibniz' x y := by
    induction x with
    | add x z hx hz => simp only [add_mul, map_add, hx, hz]; abel
    | tmul t a =>
      induction y with
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]; abel
      | tmul t' b =>
        have ea : t ⊗ₜ[R] a = t • ((1 : T) ⊗ₜ[R] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have eb : t' ⊗ₜ[R] b = t' • ((1 : T) ⊗ₜ[R] b) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have eab : (1 : S) ⊗ₜ[R] (a * b) = ((1 : S) ⊗ₜ[R] a) * ((1 : S) ⊗ₜ[R] b) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        rw [Algebra.TensorProduct.tmul_mul_tmul, mapLin_tmul, mapLin_tmul, mapLin_tmul, ea, eb,
          smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, eab, d.leibniz', map_add,
          tensorMap_mul, tensorMap_mul, tensorMap_one_tmul, tensorMap_one_tmul]

theorem mapDer_add (d e : JordanDerivation S (S ⊗[R] A)) :
    mapDer φ (d + e) = mapDer φ d + mapDer φ e :=
  JordanDerivation.ext fun x =>
    LinearMap.congr_fun (mapLin_add φ (d : S ⊗[R] A →ₗ[S] S ⊗[R] A) e) x

theorem mapDer_lie (d e : JordanDerivation S (S ⊗[R] A)) :
    mapDer φ ⁅d, e⁆ = ⁅mapDer φ d, mapDer φ e⁆ := by
  refine JordanDerivation.ext fun x => ?_
  have h : mapLin φ ((d : S ⊗[R] A →ₗ[S] S ⊗[R] A) ∘ₗ (e : S ⊗[R] A →ₗ[S] S ⊗[R] A) -
      (e : S ⊗[R] A →ₗ[S] S ⊗[R] A) ∘ₗ (d : S ⊗[R] A →ₗ[S] S ⊗[R] A)) =
      mapLin φ (d : _ →ₗ[S] _) ∘ₗ mapLin φ (e : _ →ₗ[S] _) -
        mapLin φ (e : _ →ₗ[S] _) ∘ₗ mapLin φ (d : _ →ₗ[S] _) := by
    rw [mapLin_sub, mapLin_comp, mapLin_comp]
  exact LinearMap.congr_fun h x

theorem mapDer_id_alg (d : JordanDerivation S (S ⊗[R] A)) : mapDer (AlgHom.id R S) d = d :=
  JordanDerivation.ext fun x =>
    LinearMap.congr_fun (mapLin_id_alg (d : S ⊗[R] A →ₗ[S] S ⊗[R] A)) x

theorem mapDer_comp_alg (χ : T →ₐ[R] U) (d : JordanDerivation S (S ⊗[R] A)) :
    mapDer (χ.comp φ) d = mapDer χ (mapDer φ d) :=
  JordanDerivation.ext fun x =>
    LinearMap.congr_fun (mapLin_comp_alg φ χ (d : S ⊗[R] A →ₗ[S] S ⊗[R] A)) x

/-- Transport along `φ` extends scalar extension of derivations from `R`. -/
theorem mapDer_baseChangeDer (d : JordanDerivation R A) :
    mapDer φ (baseChangeDer S d) = baseChangeDer T d :=
  JordanDerivation.ext fun x => LinearMap.congr_fun (mapLin_baseChange φ (d : A →ₗ[R] A)) x

end MapDer

end JordanAlgebra.BaseChange
