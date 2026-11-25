module

public import JordanDiagram.Diagram.Functor
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The diagram group functor is representable

Let `F` be a diagram over `k` whose nodes are free with finite bases `bᵢ`. Over the polynomial
ring `P` in the entries of two matrices `Xᵢ`, `Yᵢ` at every node, the generic matrix `Xᵢ` gives a
`P`-linear endomorphism `Gᵢ` of `P ⊗ F(i)` in the base-changed basis. The **relations** are the
basis coordinates of the generic defects: `XᵢYᵢ - 1`, `YᵢXᵢ - 1`, the failure of `Gᵢ` to be
multiplicative on pairs of basis vectors, and the failure of the `Gᵢ` to commute with the arrows
on basis vectors. The quotient `B = P ⧸ (relations)` corepresents `G_F`:

* `aeval_rels_iff`: a point kills the relations exactly when its matrices are inverse to each other
  and the maps they define are multiplicative and natural on basis vectors (`Good`).
* `goodEquiv`: such points are exactly the diagram automorphisms of `S ⊗ F`.
* `algHomEquiv`: a natural bijection `(B →ₐ[k] S) ≃ G_F(S)` for every commutative `k`-algebra `S`,
  natural in `S` (`algHomEquiv_comp`); `B` is of finite type when the shape has finitely many
  objects (`finiteType`).
* `glEquiv`, `toRep`, `glEquiv_comp_toRep`: the quotient `k[∏ GL]` of `P` by the inverse
  relations alone represents `∏ᵢ GL(F(i))`, and `B` is a further quotient compatibly with the
  inclusion `G_F ⊆ ∏ᵢ GL(F(i))`: the diagram group is a closed subgroup of `∏ᵢ GL(F(i))`.
* `JordanDiagram.representable`: the same, packaged without a choice of bases.

The group structure on `B →ₐ[k] S` is the one transported from `G_F(S)`; that it comes from a Hopf
algebra structure on `B` is the Yoneda lemma, and is not spelled out here.
-/

@[expose] public section

universe u u' v w w' x

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange TensorProduct

namespace JordanDiagram.Representability

variable {k : Type u} [CommRing k] {I : Type w} [Category.{w'} I]
variable (F : JordanDiagram.{u, v} k I) {ι : I → Type x} [∀ i, Fintype (ι i)]
  [∀ i, DecidableEq (ι i)] (b : ∀ i, Module.Basis (ι i) k (F.obj i))

variable (ι) in
/-- The variables: the entries `(a, c)` of the matrix `Xᵢ` (`true`) and of `Yᵢ` (`false`). -/
abbrev Var : Type (max w x) := Σ i : I, Bool × ι i × ι i

/-- The matrix of a point `v : Var → S` at node `i`: `Xᵢ` for `e = true`, `Yᵢ` for `e = false`. -/
def mat {S : Type*} (v : Var ι → S) (e : Bool) (i : I) : Matrix (ι i) (ι i) S :=
  Matrix.of fun a c => v ⟨i, e, a, c⟩

section Endo

variable (S : Type u') [CommRing S] [Algebra k S]

/-- The base-changed basis `1 ⊗ bᵢ` of `S ⊗ F(i)`. -/
noncomputable abbrev bS (i : I) : Module.Basis (ι i) S (S ⊗[k] F.obj i) := (b i).baseChange S

/-- The `S`-linear endomorphism of `S ⊗ F(i)` with matrix `M` in the basis `1 ⊗ bᵢ`. -/
noncomputable def endo (i : I) (M : Matrix (ι i) (ι i) S) : S ⊗[k] F.obj i →ₗ[S] S ⊗[k] F.obj i :=
  Matrix.toLin (bS F b S i) (bS F b S i) M

variable {F b S}

theorem endo_basis (i : I) (M : Matrix (ι i) (ι i) S) (a : ι i) :
    endo F b S i M (bS F b S i a) = ∑ d, M d a • bS F b S i d :=
  Matrix.toLin_self _ _ M a

variable {T : Type*} [CommRing T] [Algebra k T]

omit [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
/-- Coordinates commute with specialization along `φ : S →ₐ[k] T`. -/
theorem repr_tensorMap (φ : S →ₐ[k] T) (i : I) (y : S ⊗[k] F.obj i) (d : ι i) :
    (bS F b T i).repr (tensorMap (F.obj i) φ y) d = φ ((bS F b S i).repr y d) := by
  induction y with
  | tmul s m => simp [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]

omit [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
theorem tensorMap_basis (φ : S →ₐ[k] T) (i : I) (a : ι i) :
    tensorMap (F.obj i) φ (bS F b S i a) = bS F b T i a := by
  simp only [Module.Basis.baseChange_apply, tensorMap_one_tmul]

/-- Specializing the endomorphism with matrix `M` gives the endomorphism with matrix `φ M`. -/
theorem tensorMap_endo (φ : S →ₐ[k] T) (i : I) (M : Matrix (ι i) (ι i) S)
    (y : S ⊗[k] F.obj i) :
    tensorMap (F.obj i) φ (endo F b S i M y) = endo F b T i (M.map φ) (tensorMap (F.obj i) φ y) := by
  rw [← (bS F b S i).sum_repr y]
  simp only [map_sum, map_smul, tensorMap_smul, endo_basis, tensorMap_basis, Finset.smul_sum,
    smul_smul, Matrix.map_apply, ← map_mul]

/-- Transport along `φ` of the endomorphism with matrix `M` is the endomorphism with matrix
`φ M`. -/
theorem mapLin_endo (φ : S →ₐ[k] T) (i : I) (M : Matrix (ι i) (ι i) S) :
    mapLin φ (endo F b S i M) = endo F b T i (M.map φ) := by
  refine (bS F b T i).ext fun a => ?_
  rw [Module.Basis.baseChange_apply, mapLin_one_tmul, ← Module.Basis.baseChange_apply,
    tensorMap_endo, tensorMap_basis, Module.Basis.baseChange_apply]

end Endo

/-! ### The relations -/

variable (k ι) in
/-- The polynomial ring in the matrix entries. -/
abbrev Poly : Type (max u w x) := MvPolynomial (Var ι) k

variable (k ι) in
/-- The generic point: every variable is itself. -/
noncomputable abbrev gen : Var ι → Poly k ι := MvPolynomial.X

variable [Invertible (2 : k)]

/-- The generic endomorphism `Gᵢ` of `P ⊗ F(i)`, with matrix `Xᵢ`. -/
noncomputable abbrev genEndo (i : I) : Poly k ι ⊗[k] F.obj i →ₗ[Poly k ι] Poly k ι ⊗[k] F.obj i :=
  endo F b (Poly k ι) i (mat (gen k ι) true i)

/-- The relations: the coordinates of `XᵢYᵢ - 1`, `YᵢXᵢ - 1`, of the failure of `Gᵢ` to be
multiplicative on pairs of basis vectors, and of the failure of the `Gᵢ` to commute with the
arrows on basis vectors. -/
def rels : Set (Poly k ι) :=
  {r | ∃ (i : I) (a c : ι i), r = (mat (gen k ι) true i * mat (gen k ι) false i - 1) a c} ∪
  {r | ∃ (i : I) (a c : ι i), r = (mat (gen k ι) false i * mat (gen k ι) true i - 1) a c} ∪
  {r | ∃ (i : I) (a a' d : ι i), r = (bS F b (Poly k ι) i).repr
    (genEndo F b i (bS F b (Poly k ι) i a * bS F b (Poly k ι) i a') -
      genEndo F b i (bS F b (Poly k ι) i a) * genEndo F b i (bS F b (Poly k ι) i a')) d} ∪
  {r | ∃ (i j : I) (α : i ⟶ j) (a : ι i) (d : ι j), r = (bS F b (Poly k ι) j).repr
    (genEndo F b j (baseChangeHom (Poly k ι) (F.map α) (bS F b (Poly k ι) i a)) -
      baseChangeHom (Poly k ι) (F.map α) (genEndo F b i (bS F b (Poly k ι) i a))) d}

/-- The representing algebra `B = P ⧸ (relations)`. -/
abbrev Rep : Type (max u w x) := Poly k ι ⧸ Ideal.span (rels F b)

variable {S : Type u'} [CommRing S] [Algebra k S]

/-- A point `v` is **good** when its matrices `Xᵢ`, `Yᵢ` are inverse to each other and the
endomorphisms `gᵢ` with matrices `Xᵢ` are multiplicative on basis vectors and commute with the
arrows on basis vectors. -/
def Good (v : Var ι → S) : Prop :=
  (∀ i, mat v true i * mat v false i = 1) ∧ (∀ i, mat v false i * mat v true i = 1) ∧
  (∀ i a a', endo F b S i (mat v true i) (bS F b S i a * bS F b S i a') =
    endo F b S i (mat v true i) (bS F b S i a) * endo F b S i (mat v true i) (bS F b S i a')) ∧
  (∀ (i j : I) (α : i ⟶ j) a, endo F b S j (mat v true j)
      (baseChangeHom S (F.map α) (bS F b S i a)) =
    baseChangeHom S (F.map α) (endo F b S i (mat v true i) (bS F b S i a)))

omit [Invertible (2 : k)] [Category.{w'} I] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
theorem mat_map (φ : Poly k ι →ₐ[k] S) (e : Bool) (i : I) :
    (mat (gen k ι) e i).map φ = mat (fun y => φ (gen k ι y)) e i := by
  ext a c
  rfl

omit [Invertible (2 : k)] [Category.{w'} I] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
theorem mat_aeval (v : Var ι → S) (e : Bool) (i : I) :
    (mat (gen k ι) e i).map (MvPolynomial.aeval (R := k) v) = mat v e i := by
  ext a c
  simp [mat]

omit [Invertible (2 : k)] [Category.{w'} I] in
theorem aeval_matRel (v : Var ι → S) (e e' : Bool) (i : I) (a c : ι i) :
    MvPolynomial.aeval (R := k) v ((mat (gen k ι) e i * mat (gen k ι) e' i - 1) a c) =
      (mat v e i * mat v e' i - 1) a c := by
  have h : (MvPolynomial.aeval (R := k) v).mapMatrix
      (mat (gen k ι) e i * mat (gen k ι) e' i - 1) = mat v e i * mat v e' i - 1 := by
    rw [map_sub, map_mul, map_one, AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, mat_aeval,
      mat_aeval]
  exact congrFun (congrFun h a) c

omit [Invertible (2 : k)] in
/-- The generic multiplicativity defect specializes to the defect at a point. -/
theorem aeval_mulRel (v : Var ι → S) (i : I) (a a' d : ι i) :
    MvPolynomial.aeval v ((bS F b (Poly k ι) i).repr
      (genEndo F b i (bS F b (Poly k ι) i a * bS F b (Poly k ι) i a') -
        genEndo F b i (bS F b (Poly k ι) i a) * genEndo F b i (bS F b (Poly k ι) i a')) d) =
    (bS F b S i).repr (endo F b S i (mat v true i) (bS F b S i a * bS F b S i a') -
      endo F b S i (mat v true i) (bS F b S i a) * endo F b S i (mat v true i) (bS F b S i a'))
      d := by
  rw [← repr_tensorMap, map_sub, tensorMap_endo, tensorMap_mul, tensorMap_mul, tensorMap_endo,
    tensorMap_endo, tensorMap_basis, tensorMap_basis, mat_aeval]

omit [Invertible (2 : k)] in
/-- The generic naturality defect specializes to the defect at a point. -/
theorem aeval_natRel (v : Var ι → S) {i j : I} (α : i ⟶ j) (a : ι i) (d : ι j) :
    MvPolynomial.aeval v ((bS F b (Poly k ι) j).repr
      (genEndo F b j (baseChangeHom (Poly k ι) (F.map α) (bS F b (Poly k ι) i a)) -
        baseChangeHom (Poly k ι) (F.map α) (genEndo F b i (bS F b (Poly k ι) i a))) d) =
    (bS F b S j).repr (endo F b S j (mat v true j) (baseChangeHom S (F.map α) (bS F b S i a)) -
      baseChangeHom S (F.map α) (endo F b S i (mat v true i) (bS F b S i a))) d := by
  rw [← repr_tensorMap, map_sub, tensorMap_endo, tensorMap_baseChangeHom, tensorMap_basis,
    tensorMap_baseChangeHom, tensorMap_endo, tensorMap_basis, mat_aeval, mat_aeval]

omit [Invertible (2 : k)] [Category.{w'} I] in
theorem matRel_iff (v : Var ι → S) (e e' : Bool) (i : I) :
    (∀ a c, (mat v e i * mat v e' i - 1) a c = 0) ↔ mat v e i * mat v e' i = 1 := by
  refine ⟨fun h => ?_, fun h a c => by rw [h, sub_self, Matrix.zero_apply]⟩
  rw [← sub_eq_zero]
  ext a c
  exact h a c

omit [Invertible (2 : k)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
theorem coord_iff {i : I} (x y : S ⊗[k] F.obj i) :
    (∀ d, (bS F b S i).repr (x - y) d = 0) ↔ x = y := by
  rw [← sub_eq_zero, ← (bS F b S i).forall_coord_eq_zero_iff]
  rfl

omit [Invertible (2 : k)] in
/-- **A point kills the relations exactly when it is good.** -/
theorem aeval_rels_iff (v : Var ι → S) :
    (∀ r ∈ rels F b, MvPolynomial.aeval v r = 0) ↔ Good F b v := by
  constructor
  · intro h
    refine ⟨fun i => (matRel_iff v true false i).1 fun a c => ?_,
      fun i => (matRel_iff v false true i).1 fun a c => ?_,
      fun i a a' => (coord_iff F b _ _).1 fun d => ?_,
      fun i j α a => (coord_iff F b _ _).1 fun d => ?_⟩
    · rw [← aeval_matRel (k := k)]
      exact h _ (Or.inl (Or.inl (Or.inl ⟨i, a, c, rfl⟩)))
    · rw [← aeval_matRel (k := k)]
      exact h _ (Or.inl (Or.inl (Or.inr ⟨i, a, c, rfl⟩)))
    · rw [← aeval_mulRel]
      exact h _ (Or.inl (Or.inr ⟨i, a, a', d, rfl⟩))
    · rw [← aeval_natRel]
      exact h _ (Or.inr ⟨i, j, α, a, d, rfl⟩)
  · rintro ⟨h1, h2, h3, h4⟩ r hr
    rcases hr with (((⟨i, a, c, rfl⟩ | ⟨i, a, c, rfl⟩) | ⟨i, a, a', d, rfl⟩) |
      ⟨i, j, α, a, d, rfl⟩)
    · rw [aeval_matRel]
      exact (matRel_iff v true false i).2 (h1 i) a c
    · rw [aeval_matRel]
      exact (matRel_iff v false true i).2 (h2 i) a c
    · rw [aeval_mulRel]
      exact (coord_iff F b _ _).2 (h3 i a a') d
    · rw [aeval_natRel]
      exact (coord_iff F b _ _).2 (h4 i j α a) d

/-! ### Good points are diagram automorphisms -/

omit [Invertible (2 : k)] in
/-- When `Xᵢ` and `Yᵢ` are inverse matrices, `gᵢ` is a linear automorphism of `S ⊗ F(i)`, with
inverse the endomorphism with matrix `Yᵢ`. -/
noncomputable def invEquiv (v : Var ι → S) (i : I) (h₁ : mat v true i * mat v false i = 1)
    (h₂ : mat v false i * mat v true i = 1) : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i :=
  LinearEquiv.ofLinearMap (endo F b S i (mat v true i)) (endo F b S i (mat v false i))
    (by rw [endo, endo, ← Matrix.toLin_mul, h₁, Matrix.toLin_one])
    (by rw [endo, endo, ← Matrix.toLin_mul, h₂, Matrix.toLin_one])

/-- At a good point, `gᵢ` is a linear automorphism of `S ⊗ F(i)`. -/
noncomputable def endoEquiv (v : Var ι → S) (hv : Good F b v) (i : I) :
    S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i :=
  invEquiv F b v i (hv.1 i) (hv.2.1 i)

omit [Invertible (2 : k)] in
theorem endoEquiv_apply (v : Var ι → S) (hv : Good F b v) (i : I) (x : S ⊗[k] F.obj i) :
    endoEquiv F b v hv i x = endo F b S i (mat v true i) x := rfl

/-- At a good point, `gᵢ` is multiplicative: it is so on pairs of basis vectors, and both sides
are bilinear. -/
theorem endo_mul (v : Var ι → S) (hv : Good F b v) (i : I) (x y : S ⊗[k] F.obj i) :
    endo F b S i (mat v true i) (x * y) =
      endo F b S i (mat v true i) x * endo F b S i (mat v true i) y := by
  have key : (LinearMap.mul S (S ⊗[k] F.obj i)).compr₂ (endo F b S i (mat v true i)) =
      (LinearMap.mul S (S ⊗[k] F.obj i)).compl₁₂ (endo F b S i (mat v true i))
        (endo F b S i (mat v true i)) :=
    LinearMap.ext_basis (bS F b S i) (bS F b S i) fun a a' => hv.2.2.1 i a a'
  exact LinearMap.congr_fun₂ key x y

omit [Invertible (2 : k)] in
/-- At a good point, the `gᵢ` commute with the arrows: they do so on basis vectors, and both sides
are linear. -/
theorem endo_naturality (v : Var ι → S) (hv : Good F b v) {i j : I} (α : i ⟶ j)
    (x : S ⊗[k] F.obj i) :
    endo F b S j (mat v true j) (baseChangeHom S (F.map α) x) =
      baseChangeHom S (F.map α) (endo F b S i (mat v true i) x) := by
  rw [← (bS F b S i).sum_repr x]
  simp only [map_sum, map_smul, hv.2.2.2 i j α]

/-- The diagram automorphism of a good point. -/
noncomputable def toAut (v : Var ι → S) (hv : Good F b v) : (F.baseChange S).autGroup :=
  ⟨fun i => ⟨endoEquiv F b v hv i, endo_mul F b v hv i⟩, fun α x => endo_naturality F b v hv α x⟩

theorem toAut_apply (v : Var ι → S) (hv : Good F b v) (i : I) (x : S ⊗[k] F.obj i) :
    (toAut F b v hv).1 i x = endo F b S i (mat v true i) x := rfl

/-- The point of a diagram automorphism: the matrices of its components and of their inverses. -/
noncomputable def ofAut (g : (F.baseChange S).autGroup) : Var ι → S :=
  fun y => LinearMap.toMatrix (bS F b S y.1) (bS F b S y.1)
    (if y.2.1 then ((g.1 y.1 : S ⊗[k] F.obj y.1 ≃ₗ[S] S ⊗[k] F.obj y.1) : _ →ₗ[S] _)
      else (((g.1 y.1)⁻¹ : jordanAut S _) : S ⊗[k] F.obj y.1 ≃ₗ[S] S ⊗[k] F.obj y.1))
    y.2.2.1 y.2.2.2

theorem mat_ofAut (g : (F.baseChange S).autGroup) (i : I) :
    mat (ofAut F b g) true i = LinearMap.toMatrix (bS F b S i) (bS F b S i)
      ((g.1 i : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) : _ →ₗ[S] _) := rfl

theorem mat_ofAut_inv (g : (F.baseChange S).autGroup) (i : I) :
    mat (ofAut F b g) false i = LinearMap.toMatrix (bS F b S i) (bS F b S i)
      ((((g.1 i)⁻¹ : jordanAut S (S ⊗[k] F.obj i)) : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) :
        _ →ₗ[S] _) := rfl

theorem endo_ofAut (g : (F.baseChange S).autGroup) (i : I) :
    endo F b S i (mat (ofAut F b g) true i) =
      ((g.1 i : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) : _ →ₗ[S] _) := by
  rw [mat_ofAut, endo, Matrix.toLin_toMatrix]

theorem good_ofAut (g : (F.baseChange S).autGroup) : Good F b (ofAut F b g) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i a a' => ?_, fun i j α a => ?_⟩
  · rw [mat_ofAut, mat_ofAut_inv, ← LinearMap.toMatrix_mul]
    convert LinearMap.toMatrix_one (bS F b S i)
    exact LinearMap.ext fun x => jordanAut.apply_inv_self (g.1 i) x
  · rw [mat_ofAut, mat_ofAut_inv, ← LinearMap.toMatrix_mul]
    convert LinearMap.toMatrix_one (bS F b S i)
    exact LinearMap.ext fun x => jordanAut.inv_apply_self (g.1 i) x
  · rw [endo_ofAut]
    exact jordanAut.map_mul (g.1 i) _ _
  · rw [endo_ofAut, endo_ofAut]
    exact g.2 α _

omit [Invertible (2 : k)] in
theorem toLinearMap_endoEquiv (v : Var ι → S) (hv : Good F b v) (i : I) :
    (endoEquiv F b v hv i : S ⊗[k] F.obj i →ₗ[S] S ⊗[k] F.obj i) = endo F b S i (mat v true i) :=
  rfl

omit [Invertible (2 : k)] in
theorem toLinearMap_endoEquiv_symm (v : Var ι → S) (hv : Good F b v) (i : I) :
    ((endoEquiv F b v hv i).symm : S ⊗[k] F.obj i →ₗ[S] S ⊗[k] F.obj i) =
      endo F b S i (mat v false i) :=
  rfl

theorem mat_ofAut_toAut (v : Var ι → S) (hv : Good F b v) (e : Bool) (i : I) :
    mat (ofAut F b (toAut F b v hv)) e i = mat v e i := by
  cases e
  · rw [mat_ofAut_inv]
    exact (congrArg (LinearMap.toMatrix (bS F b S i) (bS F b S i))
      (toLinearMap_endoEquiv_symm F b v hv i)).trans (LinearMap.toMatrix_toLin _ _ _)
  · rw [mat_ofAut]
    exact (congrArg (LinearMap.toMatrix (bS F b S i) (bS F b S i))
      (toLinearMap_endoEquiv F b v hv i)).trans (LinearMap.toMatrix_toLin _ _ _)

/-- Good points are diagram automorphisms. -/
noncomputable def goodEquiv : {v : Var ι → S // Good F b v} ≃ (F.baseChange S).autGroup where
  toFun v := toAut F b v.1 v.2
  invFun g := ⟨ofAut F b g, good_ofAut F b g⟩
  left_inv v := by
    obtain ⟨v, hv⟩ := v
    refine Subtype.ext (funext fun ⟨i, e, a, c⟩ => ?_)
    exact congrFun (congrFun (mat_ofAut_toAut F b v hv e i) a) c
  right_inv g := Subtype.ext (funext fun i => jordanAut.ext fun x => by
    change endo F b S i (mat (ofAut F b g) true i) x = g.1 i x
    rw [endo_ofAut]
    rfl)

theorem goodEquiv_apply (v : {v : Var ι → S // Good F b v}) (i : I) (x : S ⊗[k] F.obj i) :
    (goodEquiv F b v).1 i x = endo F b S i (mat v.1 true i) x := rfl

/-! ### The representing algebra -/

omit [Invertible (2 : k)] [Category.{w'} I] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
theorem aeval_quotient_mk (R : Set (Poly k ι)) (f : Poly k ι ⧸ Ideal.span R →ₐ[k] S)
    (r : Poly k ι) :
    MvPolynomial.aeval (fun y => f (Ideal.Quotient.mk _ (gen k ι y))) r =
      f (Ideal.Quotient.mk _ r) := by
  have h : MvPolynomial.aeval (fun y => f (Ideal.Quotient.mk _ (gen k ι y))) =
      f.comp (Ideal.Quotient.mkₐ k (Ideal.span R)) :=
    MvPolynomial.algHom_ext fun y => by simp
  rw [h]
  rfl

omit [Invertible (2 : k)] [Category.{w'} I] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] in
variable (k) in
/-- Algebra maps out of `P ⧸ (R)` are the points killing `R`. -/
noncomputable def quotEquiv (R : Set (Poly k ι)) :
    (Poly k ι ⧸ Ideal.span R →ₐ[k] S) ≃ {v : Var ι → S // ∀ r ∈ R, MvPolynomial.aeval v r = 0} where
  toFun f := ⟨fun y => f (Ideal.Quotient.mk _ (gen k ι y)), fun r hr => by
    rw [aeval_quotient_mk, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hr), map_zero]⟩
  invFun v := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v.1) fun a ha =>
    RingHom.mem_ker.1 (Ideal.span_le.2 (fun r hr => RingHom.mem_ker.2 (v.2 r hr)) ha)
  left_inv f := Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun y =>
    MvPolynomial.aeval_X (fun y => f (Ideal.Quotient.mk _ (gen k ι y))) y)
  right_inv v := Subtype.ext (funext fun y => MvPolynomial.aeval_X v.1 y)

/-- **Representability**: algebra maps from the representing algebra `B` to `S` are exactly the
diagram automorphisms of `S ⊗ F`. -/
noncomputable def algHomEquiv : (Rep F b →ₐ[k] S) ≃ (F.baseChange S).autGroup :=
  (quotEquiv k (rels F b)).trans
    ((Equiv.subtypeEquivRight fun v => aeval_rels_iff F b v).trans (goodEquiv F b))

theorem algHomEquiv_apply (f : Rep F b →ₐ[k] S) (i : I) (x : S ⊗[k] F.obj i) :
    (algHomEquiv F b f).1 i x =
      endo F b S i (mat (fun y => f (Ideal.Quotient.mk _ (gen k ι y))) true i) x := rfl

/-- **Naturality in the base**: composing with `χ : S →ₐ[k] T` corresponds to `G_F(χ)`. -/
theorem algHomEquiv_comp {T : Type u'} [CommRing T] [Algebra k T] (χ : S →ₐ[k] T)
    (f : Rep F b →ₐ[k] S) :
    algHomEquiv F b (χ.comp f) = autMap F χ (algHomEquiv F b f) := by
  refine Subtype.ext (funext fun i => jordanAut.ext fun x => ?_)
  rw [algHomEquiv_apply, autMap_apply, mapAut_apply]
  change _ = mapLin χ (endo F b S i (mat (fun y => f (Ideal.Quotient.mk _ (gen k ι y))) true i)) x
  rw [mapLin_endo]
  rfl

omit [Invertible (2 : k)] in
/-- With finitely many objects, the representing algebra is of finite type. -/
theorem finiteType [Finite I] : Algebra.FiniteType k (Rep F b) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)

/-! ### A closed subgroup of `∏ᵢ GL(F(i))` -/

variable (ι) in
/-- The inverse relations alone: the coordinates of `XᵢYᵢ - 1` and `YᵢXᵢ - 1`. -/
def relsGL : Set (Poly k ι) :=
  {r | ∃ (i : I) (a c : ι i), r = (mat (gen k ι) true i * mat (gen k ι) false i - 1) a c} ∪
  {r | ∃ (i : I) (a c : ι i), r = (mat (gen k ι) false i * mat (gen k ι) true i - 1) a c}

variable (k ι) in
/-- The coordinate ring of `∏ᵢ GL(F(i))`: matrices `Xᵢ` with chosen inverses `Yᵢ`. -/
abbrev RepGL : Type (max u w x) := Poly k ι ⧸ Ideal.span (relsGL (k := k) ι)

omit [Invertible (2 : k)] in
theorem relsGL_subset : relsGL (k := k) ι ⊆ rels F b := fun _ hr => Or.inl (Or.inl hr)

omit [Invertible (2 : k)] in
/-- The quotient map `k[∏ GL] → B`: the diagram group is the closed subgroup cut out by the
remaining relations. -/
noncomputable def toRep : RepGL k ι →ₐ[k] Rep F b :=
  Ideal.Quotient.factorₐ k (Ideal.span_mono (relsGL_subset F b))

omit [Invertible (2 : k)] in
theorem toRep_surjective : Function.Surjective (toRep F b) :=
  Ideal.Quotient.factor_surjective (Ideal.span_mono (relsGL_subset F b))

omit [Invertible (2 : k)] [Category.{w'} I] in
theorem aeval_relsGL_iff (v : Var ι → S) :
    (∀ r ∈ relsGL (k := k) ι, MvPolynomial.aeval v r = 0) ↔
      ∀ i, mat v true i * mat v false i = 1 ∧ mat v false i * mat v true i = 1 := by
  constructor
  · intro h i
    refine ⟨(matRel_iff v true false i).1 fun a c => ?_, (matRel_iff v false true i).1 fun a c => ?_⟩
    · rw [← aeval_matRel (k := k)]
      exact h _ (Or.inl ⟨i, a, c, rfl⟩)
    · rw [← aeval_matRel (k := k)]
      exact h _ (Or.inr ⟨i, a, c, rfl⟩)
  · rintro h r (⟨i, a, c, rfl⟩ | ⟨i, a, c, rfl⟩)
    · rw [aeval_matRel]
      exact (matRel_iff v true false i).2 (h i).1 a c
    · rw [aeval_matRel]
      exact (matRel_iff v false true i).2 (h i).2 a c

/-- The point of a family of linear automorphisms: their matrices and those of their inverses. -/
noncomputable def ofGL (g : ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) : Var ι → S :=
  fun y => LinearMap.toMatrix (bS F b S y.1) (bS F b S y.1)
    (if y.2.1 then (g y.1 : _ →ₗ[S] _) else ((g y.1).symm : _ →ₗ[S] _)) y.2.2.1 y.2.2.2

omit [Invertible (2 : k)] in
theorem mat_ofGL (g : ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) (i : I) :
    mat (ofGL F b g) true i = LinearMap.toMatrix (bS F b S i) (bS F b S i)
      (g i : S ⊗[k] F.obj i →ₗ[S] S ⊗[k] F.obj i) := rfl

omit [Invertible (2 : k)] in
theorem mat_ofGL_symm (g : ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) (i : I) :
    mat (ofGL F b g) false i = LinearMap.toMatrix (bS F b S i) (bS F b S i)
      ((g i).symm : S ⊗[k] F.obj i →ₗ[S] S ⊗[k] F.obj i) := rfl

omit [Invertible (2 : k)] in
theorem ofGL_inv (g : ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) (i : I) :
    mat (ofGL F b g) true i * mat (ofGL F b g) false i = 1 ∧
      mat (ofGL F b g) false i * mat (ofGL F b g) true i = 1 := by
  refine ⟨?_, ?_⟩
  · rw [mat_ofGL, mat_ofGL_symm, ← LinearMap.toMatrix_mul]
    convert LinearMap.toMatrix_one (bS F b S i)
    exact LinearMap.ext fun x => (g i).apply_symm_apply x
  · rw [mat_ofGL, mat_ofGL_symm, ← LinearMap.toMatrix_mul]
    convert LinearMap.toMatrix_one (bS F b S i)
    exact LinearMap.ext fun x => (g i).symm_apply_apply x

omit [Invertible (2 : k)] in
theorem mat_ofGL_invEquiv (v : Var ι → S)
    (hv : ∀ i, mat v true i * mat v false i = 1 ∧ mat v false i * mat v true i = 1)
    (e : Bool) (i : I) :
    mat (ofGL F b fun i => invEquiv F b v i (hv i).1 (hv i).2) e i = mat v e i := by
  cases e
  · rw [mat_ofGL_symm]
    exact (congrArg (LinearMap.toMatrix (bS F b S i) (bS F b S i))
      (show ((invEquiv F b v i (hv i).1 (hv i).2).symm : S ⊗[k] F.obj i →ₗ[S] _) =
        endo F b S i (mat v false i) from rfl)).trans (LinearMap.toMatrix_toLin _ _ _)
  · rw [mat_ofGL]
    exact (congrArg (LinearMap.toMatrix (bS F b S i) (bS F b S i))
      (show (invEquiv F b v i (hv i).1 (hv i).2 : S ⊗[k] F.obj i →ₗ[S] _) =
        endo F b S i (mat v true i) from rfl)).trans (LinearMap.toMatrix_toLin _ _ _)

omit [Invertible (2 : k)] in
/-- Points with inverse matrices are families of linear automorphisms. -/
noncomputable def invPointEquiv :
    {v : Var ι → S // ∀ i, mat v true i * mat v false i = 1 ∧ mat v false i * mat v true i = 1} ≃
      ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i where
  toFun v i := invEquiv F b v.1 i (v.2 i).1 (v.2 i).2
  invFun g := ⟨ofGL F b g, ofGL_inv F b g⟩
  left_inv v := by
    obtain ⟨v, hv⟩ := v
    refine Subtype.ext (funext fun ⟨i, e, a, c⟩ => ?_)
    exact congrFun (congrFun (mat_ofGL_invEquiv F b v hv e i) a) c
  right_inv g := funext fun i => LinearEquiv.ext fun x => by
    change endo F b S i (mat (ofGL F b g) true i) x = g i x
    rw [mat_ofGL, endo, Matrix.toLin_toMatrix]
    rfl

omit [Invertible (2 : k)] in
/-- **`k[∏ GL]` represents `∏ᵢ GL(F(i))`**: algebra maps out of it are families of linear
automorphisms of the `S ⊗ F(i)`. -/
noncomputable def glEquiv : (RepGL k ι →ₐ[k] S) ≃ ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i :=
  (quotEquiv k (relsGL (k := k) ι)).trans
    ((Equiv.subtypeEquivRight fun v => aeval_relsGL_iff v).trans (invPointEquiv F b))

/-- **The diagram group is a closed subgroup of `∏ᵢ GL(F(i))`**: a point of the representing
algebra, seen as a point of `k[∏ GL]` through the quotient map, is the family of linear
automorphisms underlying the corresponding diagram automorphism. -/
theorem glEquiv_comp_toRep (f : Rep F b →ₐ[k] S) (i : I) :
    glEquiv F b (f.comp (toRep F b)) i =
      ((algHomEquiv F b f).1 i : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) :=
  LinearEquiv.ext fun _ => rfl

end JordanDiagram.Representability

namespace JordanDiagram

open Representability

variable {k : Type u} [CommRing k] [Invertible (2 : k)] {I : Type w} [Category.{w'} I]

/-- **Representability of the diagram group functor.** For a diagram with finite free nodes there
is a commutative `k`-algebra `B` such that algebra maps `B → S` are naturally the diagram
automorphisms of `S ⊗ F`, for every commutative `k`-algebra `S`; `B` is of finite type when the
shape has finitely many objects; and `B` is a quotient of an algebra `A` representing
`∏ᵢ GL(F(i))`, compatibly with the inclusion of `G_F` into `∏ᵢ GL(F(i))`, so that the diagram
group scheme `Spec B` is a closed subgroup scheme of `∏ᵢ GL(F(i))`. -/
theorem representable (F : JordanDiagram.{u, v} k I) [∀ i, Module.Free k (F.obj i)]
    [∀ i, Module.Finite k (F.obj i)] :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra k B)
      (e : ∀ (S : Type u') [CommRing S] [Algebra k S], (B →ₐ[k] S) ≃ (F.baseChange S).autGroup),
      (∀ (S T : Type u') [CommRing S] [Algebra k S] [CommRing T] [Algebra k T] (χ : S →ₐ[k] T)
        (f : B →ₐ[k] S), e T (χ.comp f) = autMap F χ (e S f)) ∧
      (Finite I → Algebra.FiniteType k B) ∧
      ∃ (A : Type (max u v w)) (_ : CommRing A) (_ : Algebra k A)
        (eGL : ∀ (S : Type u') [CommRing S] [Algebra k S],
          (A →ₐ[k] S) ≃ ∀ i, S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i)
        (π : A →ₐ[k] B), Function.Surjective π ∧
        ∀ (S : Type u') [CommRing S] [Algebra k S] (f : B →ₐ[k] S) (i : I),
          eGL S (f.comp π) i = ((e S f).1 i : S ⊗[k] F.obj i ≃ₗ[S] S ⊗[k] F.obj i) := by
  classical
  let b := fun i => Module.Free.chooseBasis k (F.obj i)
  exact ⟨Rep F b, inferInstance, inferInstance, fun S _ _ => algHomEquiv F b,
    fun S T _ _ _ _ χ f => algHomEquiv_comp F b χ f, fun _ => finiteType F b,
    RepGL k _, inferInstance, inferInstance, fun S _ _ => glEquiv F b, toRep F b,
    toRep_surjective F b, fun S _ _ f i => glEquiv_comp_toRep F b f i⟩

end JordanDiagram
