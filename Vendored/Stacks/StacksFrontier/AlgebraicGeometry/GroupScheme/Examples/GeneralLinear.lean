module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecRingHomEquiv

/-!
# The general linear group scheme

The general linear scheme of rank `n` over the integers is the spectrum of the polynomial ring
in the entries of an `n` by `n` matrix, localized at the determinant of the generic matrix. It
represents the functor sending a scheme to the group of invertible `n` by `n` matrices over its
ring of global sections, matrix multiplication makes it a group scheme, and over an arbitrary
base scheme it is obtained from the integral model by base change.

## Main definitions

* `AlgebraicGeometry.generalLinearDeterminant` is the determinant of the generic matrix,
  `AlgebraicGeometry.generalLinearCoordinateRing` the coordinate ring obtained by inverting it,
  and `AlgebraicGeometry.generalLinearScheme` the general linear scheme itself.
* `AlgebraicGeometry.generalLinearGroupFunctor` sends a scheme to the general linear group of
  its ring of global sections.
* `AlgebraicGeometry.generalLinearStructureMorphism` is the structural morphism to `Spec ℤ` and
  `AlgebraicGeometry.generalLinearTensorSquare` the tensor square of the coordinate ring.
* `AlgebraicGeometry.generalLinearBaseChange` is the base-changed group scheme as an object
  over `S`, `AlgebraicGeometry.generalLinearGroupOverFunctor` assigns invertible matrices over
  global sections to an `S`-scheme, and `AlgebraicGeometry.generalLinearCoordinateSection` is
  the generic matrix entry as a global section of the integral model.

## Main results

* `AlgebraicGeometry.generalLinearGroup_representableBy_generalLinearScheme` identifies the
  general linear scheme as a representing object for the general linear group functor.
* `AlgebraicGeometry.generalLinearSchemeGrpObj` is the group-object structure over `Spec ℤ`, and
  `AlgebraicGeometry.exists_multiplicationRingHom` identifies its multiplication with the
  spectrum of the coordinate-ring map given by matrix multiplication.
* `AlgebraicGeometry.generalLinearBaseChangeGrpObj` is the base-changed group-object structure,
  `AlgebraicGeometry.baseChangePointsIsoGeneralLinearPoints` identifies the underlying points by
  the pullback universal property, and `AlgebraicGeometry.baseChangeGroupPointsIso` identifies
  the group-valued functor of points with invertible matrices, naturally in the `S`-scheme.

## Implementation notes

The generic matrix is Mathlib's `Matrix.mvPolynomialX`, indexed by `Fin n`, and the integers are
represented by `ULift.{u} ℤ`, so the construction lives in `Scheme.{u}` for any universe `u`. A
group scheme over `S` is a group object in schemes over `S`; the underlying scheme of
`generalLinearBaseChange` is the fibre product over `Spec ℤ`.

The existential in `exists_multiplicationRingHom` packages the contravariant coordinate-ring map
together with both its effect on the generic matrix entries and the assertion that it induces
the group multiplication, which records the formula independently of any particular construction
of the localization lift. The set-valued base-change comparison is characterized by composition
with the first pullback projection, so it has the orientation asserted in the source, and the
group-valued comparison sends a point to the matrix obtained by pulling back each generic
coordinate along that projection; this also pins down multiplication, units and inverses without
allowing a twist by a group automorphism.

All statements include `n = 0`, where the same constructions give the trivial group scheme.

## References

* [Stacks Project, Tag 022W](https://stacks.math.columbia.edu/tag/022W)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  MonObj Opposite

namespace AlgebraicGeometry

/-- The determinant of the generic `n` by `n` matrix over the integers. -/
@[sga "3 I 4.5" "partial"]
noncomputable abbrev generalLinearDeterminant (n : ℕ) :
    MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ) :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) (ULift.{u} ℤ))

/-- The coordinate ring of the general linear scheme: the generic matrix ring with its
determinant inverted. -/
@[sga "3 I 4.5" "coordinate ring Z[T_ij"]
noncomputable abbrev generalLinearCoordinateRing (n : ℕ) : Type u :=
  Localization.Away (generalLinearDeterminant.{u} n)

/-- The general linear scheme `GL_n` over the integers. -/
@[stacks 022W "general_linear_scheme"]
noncomputable abbrev generalLinearScheme (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (generalLinearCoordinateRing.{u} n))

/-- Evaluating the generic determinant at a matrix of values gives the determinant of that
matrix. -/
lemma localizedPolynomial_det_eval {n : ℕ} {A : Type u} [CommRing A]
    (f : MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ) →+* A) :
    f (generalLinearDeterminant.{u} n) = (Matrix.of fun i j => f (MvPolynomial.X (i, j))).det := by
  change f (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) (ULift.{u} ℤ))) = _
  rw [RingHom.map_det]
  congr 1

/-- Evaluation of the generic matrix ring at the entries of an invertible matrix. -/
noncomputable def polynomialEvalOfGeneralLinear (n : ℕ) (A : Type u) [CommRing A]
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ) →+* A :=
  MvPolynomial.eval₂Hom ((algebraMap ℤ A).comp ULift.ringEquiv.toRingHom)
    (fun ij => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2)

/-- Every homomorphism out of the general linear coordinate ring is the identity on the
coefficient ring. -/
lemma localizedPolynomial_coeff_map (n : ℕ) (A : Type u) [CommRing A]
    (f : generalLinearCoordinateRing.{u} n →+* A) :
    f.comp (algebraMap (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)) =
      (algebraMap ℤ A).comp ULift.ringEquiv.toRingHom := by
  ext z
  obtain ⟨z⟩ := z
  have h : (f.comp (algebraMap (ULift.{u} ℤ)
      (generalLinearCoordinateRing.{u} n))).comp
        ULift.ringEquiv.symm.toRingHom = (algebraMap ℤ A) := RingHom.ext_int _ _
  exact congrArg (fun q : ℤ →+* A => q (ULift.ringEquiv.{0, u} (ULift.up.{u, 0} z))) h

/-- The homomorphism from the general linear coordinate ring attached to an invertible
matrix. -/
noncomputable def localizedPolynomialHomOfGeneralLinear (n : ℕ) (A : Type u)
    [CommRing A] (g : Matrix.GeneralLinearGroup (Fin n) A) :
    generalLinearCoordinateRing.{u} n →+* A := by
  let d := generalLinearDeterminant.{u} n
  let p := polynomialEvalOfGeneralLinear n A g
  have hd : IsUnit (p d) := by
    rw [localizedPolynomial_det_eval]
    have hM : (Matrix.of fun i j => p (MvPolynomial.X (i, j))) =
        (g : Matrix (Fin n) (Fin n) A) := by
      ext i j
      simp [p, polynomialEvalOfGeneralLinear]
    rw [hM]
    exact (Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin n) (Fin n) A)).mp g.isUnit
  exact IsLocalization.Away.lift d hd

/-- The invertible matrix attached to a homomorphism out of the general linear coordinate
ring. -/
noncomputable def generalLinearOfLocalizedPolynomialHom (n : ℕ) (A : Type u)
    [CommRing A] (f : generalLinearCoordinateRing.{u} n →+* A) :
    Matrix.GeneralLinearGroup (Fin n) A := by
  let P := MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ)
  let d := generalLinearDeterminant.{u} n
  let p : P →+* A := f.comp (algebraMap P (Localization.Away d))
  let M : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => p (MvPolynomial.X (i, j))
  have hdet : IsUnit M.det := by
    rw [← localizedPolynomial_det_eval p]
    exact (IsLocalization.Away.algebraMap_isUnit d).map f
  exact ((Matrix.isUnit_iff_isUnit_det M).2 hdet).unit

private lemma generalLinearOfLocalizedPolynomialHom_entry (n : ℕ) (A : Type u)
    [CommRing A] (f : generalLinearCoordinateRing.{u} n →+* A) (i j : Fin n) :
    ((generalLinearOfLocalizedPolynomialHom n A f : Matrix (Fin n) (Fin n) A) i j) =
      f (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
        (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, j))) := by
  simp [generalLinearOfLocalizedPolynomialHom]

/-- Homomorphisms out of the general linear coordinate ring are exactly invertible matrices. -/
noncomputable def localizedPolynomialHomEquiv (n : ℕ) (A : Type u) [CommRing A] :
    (generalLinearCoordinateRing.{u} n →+* A) ≃ Matrix.GeneralLinearGroup (Fin n) A where
  toFun f := generalLinearOfLocalizedPolynomialHom n A f
  invFun g := localizedPolynomialHomOfGeneralLinear n A g
  left_inv f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (generalLinearDeterminant.{u} n))
    let P := MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ)
    let d := generalLinearDeterminant.{u} n
    let g := generalLinearOfLocalizedPolynomialHom n A f
    change (localizedPolynomialHomOfGeneralLinear n A g).comp
        (algebraMap P (Localization.Away d)) =
      f.comp (algebraMap P (Localization.Away d))
    rw [localizedPolynomialHomOfGeneralLinear, IsLocalization.Away.lift_comp]
    apply MvPolynomial.ringHom_ext'
    · calc
        (polynomialEvalOfGeneralLinear n A g).comp MvPolynomial.C =
            (algebraMap ℤ A).comp ULift.ringEquiv.toRingHom := by
              rw [polynomialEvalOfGeneralLinear, MvPolynomial.eval₂Hom_comp_C]
        _ = (f.comp (algebraMap P (Localization.Away d))).comp MvPolynomial.C := by
              rw [← localizedPolynomial_coeff_map n A f]
              ext z
              rw [MvPolynomial.C_eq_algebraMap]
              change f ((algebraMap (ULift.{u} ℤ) (Localization.Away d)) z) =
                f ((algebraMap P (Localization.Away d)) ((algebraMap (ULift.{u} ℤ) P) z))
              rw [← IsScalarTower.algebraMap_apply (ULift.{u} ℤ) P (Localization.Away d) z]
    · intro ij
      have hg : (g : Matrix (Fin n) (Fin n) A) =
          Matrix.of fun i j => (f.comp (algebraMap P (Localization.Away d)))
            (MvPolynomial.X (i, j)) := by
        dsimp [g, generalLinearOfLocalizedPolynomialHom]
      rw [polynomialEvalOfGeneralLinear, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      change (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2 = _
      rw [hg]
      rfl
  right_inv g := by
    apply Units.ext
    ext i j
    simp [localizedPolynomialHomOfGeneralLinear, generalLinearOfLocalizedPolynomialHom,
      polynomialEvalOfGeneralLinear]

/-- The product of two invertible matrices attached to coordinate-ring homomorphisms has the
expected entries. -/
lemma localizedPolynomialHomEquiv_mul_entry (n : ℕ) (A : Type u) [CommRing A]
    (f g : generalLinearCoordinateRing.{u} n →+* A) (i j : Fin n) :
    (((localizedPolynomialHomEquiv n A f * localizedPolynomialHomEquiv n A g :
      Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) =
      ∑ k : Fin n,
        f (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, k))) *
        g (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (k, j))) := by
  simp [Units.val_mul, Matrix.mul_apply, localizedPolynomialHomEquiv,
    generalLinearOfLocalizedPolynomialHom_entry]

/-- Morphisms from a scheme to the general linear scheme are exactly homomorphisms from its
coordinate ring to the ring of global sections.  This is
`AlgebraicGeometry.specRingHomEquiv` at the coordinate ring of `GL_n`. -/
noncomputable def schemeHomRingHomEquiv (n : ℕ) {X : Scheme.{u}} :
    (X ⟶ generalLinearScheme.{u} n) ≃
      (generalLinearCoordinateRing.{u} n →+* Scheme.Γ.obj (op X)) :=
  specRingHomEquiv (generalLinearCoordinateRing.{u} n) X

/-- The homomorphism attached to a composite `f ≫ g` is the homomorphism attached to `g`
followed by the map on global sections induced by `f`. -/
lemma schemeHomRingHomEquiv_comp (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ generalLinearScheme.{u} n) :
    schemeHomRingHomEquiv n (f ≫ g) =
      (Scheme.Γ.map f.op).hom.comp (schemeHomRingHomEquiv n g) :=
  specRingHomEquiv_comp (generalLinearCoordinateRing.{u} n) f g

/-- The homomorphism attached to a morphism of affine schemes is the given coordinate-ring map
followed by the global-sections isomorphism. -/
lemma schemeHomRingHomEquiv_specMap (n : ℕ) {B : Type u} [CommRing B]
    (φ : generalLinearCoordinateRing.{u} n →+* B) :
    schemeHomRingHomEquiv n (Spec.map (CommRingCat.ofHom φ)) =
      (Scheme.ΓSpecIso (.of B)).inv.hom.comp φ :=
  specRingHomEquiv_specMap (generalLinearCoordinateRing.{u} n) φ

/-- The invertible matrix attached to `ρ.comp φ` is the image under `ρ` of the invertible matrix
attached to `φ`. -/
lemma localizedPolynomialHomEquiv_comp (n : ℕ) {A B : Type u} [CommRing A] [CommRing B]
    (φ : generalLinearCoordinateRing.{u} n →+* A) (ρ : A →+* B) :
    localizedPolynomialHomEquiv n B (ρ.comp φ) =
      Matrix.GeneralLinearGroup.map ρ (localizedPolynomialHomEquiv n A φ) := by
  apply Units.ext
  ext i j
  simp [localizedPolynomialHomEquiv, generalLinearOfLocalizedPolynomialHom,
    Matrix.GeneralLinearGroup.map_apply, IsUnit.unit_spec]

/-- The functor assigning to a scheme the group of invertible `n` by `n` matrices over its
ring of global sections. -/
def generalLinearGroupFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u} where
  obj X := GrpCat.of (Matrix.GeneralLinearGroup (Fin n) (Scheme.Γ.obj X))
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map (Scheme.Γ.map f).hom)
  map_id X := by
    ext A i j
    rfl
  map_comp f g := by
    ext A i j
    rfl

/-- The general linear scheme, as a representing object for the general linear group
functor. -/
noncomputable def generalLinearRepresentableBy (n : ℕ) :
    Functor.RepresentableBy (generalLinearGroupFunctor.{u} n ⋙ forget GrpCat)
      (generalLinearScheme.{u} n) where
  homEquiv {X} := (schemeHomRingHomEquiv n).trans
    (localizedPolynomialHomEquiv n (Scheme.Γ.obj (op X)))
  homEquiv_comp {X Y} f g := by
    change localizedPolynomialHomEquiv n (Scheme.Γ.obj (op X))
      (schemeHomRingHomEquiv n (f ≫ g)) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map f.op).hom
        (localizedPolynomialHomEquiv n (Scheme.Γ.obj (op Y)) (schemeHomRingHomEquiv n g))
    rw [schemeHomRingHomEquiv_comp]
    exact localizedPolynomialHomEquiv_comp n _ _

/-- **Stacks Project, Tag 022W.** The functor of invertible `n` by `n`
matrices over global sections is represented by the general linear scheme `GL_n`. -/
@[stacks 022W "representability", sga "3 XX 5.1" "special case"]
theorem generalLinearGroup_representableBy_generalLinearScheme (n : ℕ) :
    Nonempty ((generalLinearGroupFunctor.{u} n ⋙ forget GrpCat).RepresentableBy
      (generalLinearScheme.{u} n)) :=
  ⟨generalLinearRepresentableBy n⟩

/-- The canonical structure morphism from the general linear scheme to the spectrum of the
integers. -/
noncomputable def generalLinearStructureMorphism (n : ℕ) :
    generalLinearScheme.{u} n ⟶ Spec (.of (ULift.{u} ℤ)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)))

/-- The tensor square of the coordinate ring, using its algebra structure over the integers. -/
noncomputable abbrev generalLinearTensorSquare (n : ℕ) : Type u :=
  @TensorProduct (ULift.{u} ℤ) CommRing.toCommSemiring
    (generalLinearCoordinateRing.{u} n) (generalLinearCoordinateRing.{u} n)
    CommRing.toCommSemiring.toAddCommMonoid CommRing.toCommSemiring.toAddCommMonoid
    Algebra.toModule Algebra.toModule

/-- The general linear scheme over `Spec ℤ`, as a representing object for the general linear
group functor on schemes over `Spec ℤ`. -/
noncomputable def generalLinearOverRepresentableBy (n : ℕ) :
    (((Over.forget (Spec (.of (ULift.{u} ℤ)))).op ⋙ generalLinearGroupFunctor.{u} n) ⋙
        forget GrpCat).RepresentableBy
      (Over.mk (generalLinearStructureMorphism.{u} n)) := by
  let h := generalLinearRepresentableBy n
  refine ⟨?_, ?_⟩
  · intro X
    let e : (X ⟶ Over.mk (generalLinearStructureMorphism.{u} n)) ≃
        (X.left ⟶ generalLinearScheme.{u} n) :=
      { toFun f := (Over.forget (Spec (.of (ULift.{u} ℤ)))).map f
        invFun f := Over.homMk f (specULiftZIsTerminal.hom_ext _ _)
        left_inv f := by ext; rfl
        right_inv f := rfl }
    exact e.trans h.homEquiv
  · intro X Y f g
    change h.homEquiv ((Over.forget _).map (f ≫ g)) =
      (generalLinearGroupFunctor.{u} n ⋙ forget GrpCat).map ((Over.forget _).map f).op
          (h.homEquiv ((Over.forget _).map g))
    exact h.homEquiv_comp ((Over.forget _).map f) ((Over.forget _).map g)

/-- **Stacks Project, Tag 022W.** The general linear scheme over the integers is a group
scheme. -/
@[stacks 022W "multiplication"]
noncomputable instance generalLinearSchemeGrpObj (n : ℕ) :
    GrpObj (Over.mk (generalLinearStructureMorphism.{u} n)) :=
  GrpObj.ofRepresentableBy (Over.mk (generalLinearStructureMorphism.{u} n))
    ((Over.forget (Spec (.of (ULift.{u} ℤ)))).op ⋙ generalLinearGroupFunctor.{u} n)
    (generalLinearOverRepresentableBy n)

/-- The multiplication of the general linear group object, read off through the representing
equivalence as the product of the two projections. -/
private lemma generalLinearMul_homEquiv (n : ℕ) :
    (generalLinearOverRepresentableBy.{u} n).homEquiv'
        (μ[Over.mk (generalLinearStructureMorphism.{u} n)]) =
      (generalLinearOverRepresentableBy.{u} n).homEquiv'
          (fst (Over.mk (generalLinearStructureMorphism.{u} n))
            (Over.mk (generalLinearStructureMorphism.{u} n))) *
        (generalLinearOverRepresentableBy.{u} n).homEquiv'
          (snd (Over.mk (generalLinearStructureMorphism.{u} n))
            (Over.mk (generalLinearStructureMorphism.{u} n))) :=
  Equiv.apply_symm_apply _ _

/-- The first projection out of `Spec` of the tensor square corresponds to the left inclusion of
the coordinate ring. -/
private lemma schemeHomRingHomEquiv_pullbackSpecIso_inv_fst (n : ℕ) :
    schemeHomRingHomEquiv n
        ((pullbackSpecIso (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)
          (generalLinearCoordinateRing.{u} n)).inv ≫ pullback.fst _ _) =
      (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
        Algebra.TensorProduct.includeLeftRingHom := by
  rw [pullbackSpecIso_inv_fst]
  exact schemeHomRingHomEquiv_specMap (n := n) (B := generalLinearTensorSquare.{u} n)
    Algebra.TensorProduct.includeLeftRingHom

/-- The second projection out of `Spec` of the tensor square corresponds to the right inclusion
of the coordinate ring. -/
private lemma schemeHomRingHomEquiv_pullbackSpecIso_inv_snd (n : ℕ) :
    schemeHomRingHomEquiv n
        ((pullbackSpecIso (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)
          (generalLinearCoordinateRing.{u} n)).inv ≫ pullback.snd _ _) =
      (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
        Algebra.TensorProduct.includeRight.toRingHom := by
  rw [pullbackSpecIso_inv_snd]
  exact schemeHomRingHomEquiv_specMap (n := n) (B := generalLinearTensorSquare.{u} n)
    Algebra.TensorProduct.includeRight.toRingHom

/-- The product of the matrices attached to the two inclusions into the tensor square has
`(i, j)` entry `∑ k, xᵢₖ ⊗ xₖⱼ`. -/
private lemma generalLinearTensorSquare_mul_entry (n : ℕ) (i j : Fin n) :
    (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).hom.hom
      (((localizedPolynomialHomEquiv n
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))
          ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
            Algebra.TensorProduct.includeLeftRingHom) *
        localizedPolynomialHomEquiv n
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))
          ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
            Algebra.TensorProduct.includeRight.toRingHom) :
        Matrix.GeneralLinearGroup (Fin n)
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))) :
        Matrix (Fin n) (Fin n)
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))) i j) =
      ∑ k : Fin n,
        @TensorProduct.tmul (ULift.{u} ℤ) CommRing.toCommSemiring
          (generalLinearCoordinateRing.{u} n) (generalLinearCoordinateRing.{u} n)
          CommRing.toCommSemiring.toAddCommMonoid
          CommRing.toCommSemiring.toAddCommMonoid
          Algebra.toModule Algebra.toModule
          (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
            (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, k)))
          (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
            (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (k, j))) := by
  have hc (x : generalLinearTensorSquare.{u} n) :
      (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).hom.hom
        ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom x) = x :=
    by simp
  rw [localizedPolynomialHomEquiv_mul_entry n
    (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))
    ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
      Algebra.TensorProduct.includeLeftRingHom)
    ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
      Algebra.TensorProduct.includeRight.toRingHom) i j]
  refine (map_sum (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).hom.hom _
    Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
  refine (map_mul (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).hom.hom _ _).trans
    ((congrArg₂ (· * ·) (hc _) (hc _)).trans ?_)
  simp [Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- **Stacks Project, Tag 022W.** Multiplication on the general linear scheme is induced by
the coordinate-ring homomorphism sending `xᵢⱼ` to `∑ k, xᵢₖ ⊗ xₖⱼ`. -/
@[stacks 022W "multiplication"]
theorem exists_multiplicationRingHom (n : ℕ) :
    ∃ f : generalLinearCoordinateRing.{u} n →+* generalLinearTensorSquare.{u} n,
      ((pullbackSpecIso (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)
          (generalLinearCoordinateRing.{u} n)).inv ≫
          μ[Over.mk (generalLinearStructureMorphism.{u} n)].left =
            Spec.map (CommRingCat.ofHom f)) ∧
        ∀ i j : Fin n,
          f (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
              (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, j))) =
            ∑ k : Fin n,
          @TensorProduct.tmul (ULift.{u} ℤ) CommRing.toCommSemiring
                (generalLinearCoordinateRing.{u} n) (generalLinearCoordinateRing.{u} n)
                CommRing.toCommSemiring.toAddCommMonoid
                CommRing.toCommSemiring.toAddCommMonoid
                Algebra.toModule Algebra.toModule
                (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
                  (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, k)))
                (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
                  (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (k, j))) := by
  let h := (pullbackSpecIso (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)
      (generalLinearCoordinateRing.{u} n)).inv ≫
    μ[Over.mk (generalLinearStructureMorphism.{u} n)].left
  let g := schemeHomRingHomEquiv n h
  let f : generalLinearCoordinateRing.{u} n →+* generalLinearTensorSquare.{u} n :=
    (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).hom.hom.comp g
  let X : Over (Spec (.of (ULift.{u} ℤ))) := Over.mk
    (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (generalLinearTensorSquare.{u} n))))
  let k : X ⟶ Over.mk (generalLinearStructureMorphism.{u} n) ⊗
      Over.mk (generalLinearStructureMorphism.{u} n) :=
    Over.homMk (pullbackSpecIso (ULift.{u} ℤ) (generalLinearCoordinateRing.{u} n)
      (generalLinearCoordinateRing.{u} n)).inv (by
        rw [Over.tensorObj_hom]
        exact AlgebraicGeometry.specULiftZIsTerminal.hom_ext _ _)
  let α := generalLinearOverRepresentableBy.{u} n
  refine ⟨f, ?_, fun i j => ?_⟩
  · apply (schemeHomRingHomEquiv n).injective
    rw [schemeHomRingHomEquiv_specMap]
    exact RingHom.ext fun x => (congrArg (fun q => q.hom (g x))
      (Iso.hom_inv_id (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))))).symm
  have hpoint : localizedPolynomialHomEquiv n
        (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n))))) g =
      localizedPolynomialHomEquiv n
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))
          ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
            Algebra.TensorProduct.includeLeftRingHom) *
        localizedPolynomialHomEquiv n
          (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))
          ((Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).inv.hom.comp
            Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← schemeHomRingHomEquiv_pullbackSpecIso_inv_fst,
      ← schemeHomRingHomEquiv_pullbackSpecIso_inv_snd]
    change α.homEquiv' (k ≫ μ[Over.mk (generalLinearStructureMorphism.{u} n)]) =
      α.homEquiv' (k ≫ fst (Over.mk (generalLinearStructureMorphism.{u} n))
          (Over.mk (generalLinearStructureMorphism.{u} n))) *
        α.homEquiv' (k ≫ snd (Over.mk (generalLinearStructureMorphism.{u} n))
          (Over.mk (generalLinearStructureMorphism.{u} n)))
    rw [α.homEquiv'_comp, α.homEquiv'_comp, α.homEquiv'_comp, generalLinearMul_homEquiv]
    exact map_mul _ _ _
  exact (congrArg (fun z : Matrix.GeneralLinearGroup (Fin n)
      (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n))))) =>
    (Scheme.ΓSpecIso (.of (generalLinearTensorSquare.{u} n))).hom.hom
      ((z : Matrix (Fin n) (Fin n)
        (Scheme.Γ.obj (op (Spec (.of (generalLinearTensorSquare.{u} n)))))) i j)) hpoint).trans
    (generalLinearTensorSquare_mul_entry n i j)

/-- The general linear group scheme over `S`, obtained by base change from `Spec ℤ`. -/
@[stacks 022W "base_change"]
noncomputable abbrev generalLinearBaseChange (n : ℕ) (S : Scheme.{u}) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj
    (Over.mk (generalLinearStructureMorphism.{u} n))

/-- The group of invertible matrices in global sections, functorially on schemes over `S`. -/
noncomputable abbrev generalLinearGroupOverFunctor (n : ℕ) (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ generalLinearGroupFunctor n

/-- The generic `(i, j)` matrix entry as a global section of the integral general linear
scheme. -/
noncomputable def generalLinearCoordinateSection (n : ℕ) (i j : Fin n) :
    Scheme.Γ.obj (Opposite.op (generalLinearScheme.{u} n)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (generalLinearCoordinateRing.{u} n))).inv
      (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
        (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, j)))

private lemma schemeHomRingHomEquiv_id (n : ℕ) :
    schemeHomRingHomEquiv n (𝟙 (generalLinearScheme.{u} n)) =
      (Scheme.ΓSpecIso (CommRingCat.of (generalLinearCoordinateRing.{u} n))).inv.hom :=
  specRingHomEquiv_id (generalLinearCoordinateRing.{u} n)

private lemma schemeHomRingHomEquiv_coordinate (n : ℕ) {X : Scheme.{u}}
    (f : X ⟶ generalLinearScheme.{u} n) (i j : Fin n) :
    schemeHomRingHomEquiv n f
        (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
          (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, j))) =
      (Scheme.Γ.map f.op).hom (generalLinearCoordinateSection n i j) := by
  have hval := congrArg (fun φ : _ →+* Scheme.Γ.obj (Opposite.op X) =>
    φ (algebraMap (MvPolynomial (Fin n × Fin n) (ULift.{u} ℤ))
      (generalLinearCoordinateRing.{u} n) (MvPolynomial.X (i, j))))
    (schemeHomRingHomEquiv_comp n f (𝟙 _))
  rwa [schemeHomRingHomEquiv_id] at hval

/-- Points of the base change are naturally points of the integral general linear scheme. -/
@[stacks 022W "base_change"]
noncomputable def baseChangePointsIsoGeneralLinearPoints (n : ℕ) (S : Scheme.{u}) :
    yoneda.obj (generalLinearBaseChange n S) ≅
      (Over.forget S).op ⋙ yoneda.obj (generalLinearScheme n) :=
  NatIso.ofComponents (fun T =>
    Equiv.toIso
      { toFun := fun f => f.left ≫ pullback.fst (generalLinearStructureMorphism.{u} n)
          (specULiftZIsTerminal.from S)
        invFun := fun f =>
          Over.homMk
            (pullback.lift f T.unop.hom (IsTerminal.hom_ext specULiftZIsTerminal _ _))
            (pullback.lift_snd _ _ _)
        left_inv f := Over.OverMorphism.ext <| pullback.hom_ext
          (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans f.w.symm)
        right_inv := fun f => pullback.lift_fst _ _ _ })
    (by
      intro T T' k
      ext f
      simp [Category.assoc])

/-- The pointwise map of the base-change comparison is composition with the first projection. -/
@[stacks 022W "base_change"]
theorem baseChangePointsIsoGeneralLinearPoints_hom_app (n : ℕ) (S : Scheme.{u})
    (T : (Over S)ᵒᵖ) (f : T.unop ⟶ generalLinearBaseChange n S) :
    (baseChangePointsIsoGeneralLinearPoints n S).hom.app T f =
      f.left ≫ pullback.fst (generalLinearStructureMorphism.{u} n)
        (specULiftZIsTerminal.from S) := by
  simp [baseChangePointsIsoGeneralLinearPoints]

/-- Base change preserves the group-scheme structure of the general linear group. -/
@[stacks 022W "base_change"]
noncomputable instance generalLinearBaseChangeGrpObj (n : ℕ) (S : Scheme.{u}) :
    GrpObj (generalLinearBaseChange n S) := by
  unfold generalLinearBaseChange
  letI : GrpObj (Over.mk (generalLinearStructureMorphism.{u} n)) :=
    generalLinearSchemeGrpObj.{u} n
  exact Over.grpObjMkPullbackSnd (f := generalLinearStructureMorphism.{u} n)
    (g := specULiftZIsTerminal.from S)

end AlgebraicGeometry

namespace CategoryTheory.Over

open scoped CategoryTheory.MonObj

universe v w

variable {C : Type v} [Category.{w} C] [HasPullbacks C]
variable {B S₀ G : C} {b : S₀ ⟶ B} {h : G ⟶ B}

/-- The cartesian monoidal structure on `Over B` given by fibre products over `B`. -/
noncomputable local instance instOverCartesianMonoidalCategoryB :
    CartesianMonoidalCategory (Over B) := Over.cartesianMonoidalCategory B

/-- The cartesian monoidal structure on `Over S₀` given by fibre products over `S₀`. -/
noncomputable local instance instOverCartesianMonoidalCategoryS :
    CartesianMonoidalCategory (Over S₀) := Over.cartesianMonoidalCategory S₀

variable [GrpObj (Over.mk h)]

/-- Points of the pullback of a group object over `S₀` are points of the group object itself
over `B`, compatibly with the group law. -/
noncomputable def pullbackPointsMulEquiv (T : Over S₀) :
    letI : GrpObj (Over.mk (pullback.snd h b)) := Over.grpObjMkPullbackSnd
    (T ⟶ Over.mk (pullback.snd h b)) ≃* ((Over.map b).obj T ⟶ Over.mk h) := by
  let P := Over.mk (pullback.snd h b)
  letI : GrpObj P := Over.grpObjMkPullbackSnd
  refine
    { toEquiv :=
        { toFun := fun f => Over.homMk (f.left ≫ pullback.fst h b) (by
            simp only [Over.mk_hom, Over.map_obj_hom]
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact congrArg (fun q => q ≫ b) f.w)
          invFun := fun g => Over.homMk
            (pullback.lift g.left T.hom g.w) (pullback.lift_snd _ _ _)
          left_inv := fun f => Over.OverMorphism.ext <| pullback.hom_ext
            (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans f.w.symm)
          right_inv := fun g => Over.OverMorphism.ext (pullback.lift_fst _ _ _) }
      map_mul' := ?_ }
  · intro f g
    simp only [CategoryTheory.Hom.mul_def, Over.grpObjMkPullbackSnd_mul]
    apply Over.OverMorphism.ext
    simp only [Over.homMk_left, Over.comp_left, Over.lift_left]
    have hfw : f.left ≫ pullback.snd h b = T.hom := f.w
    have hgw : g.left ≫ pullback.snd h b = T.hom := g.w
    have hf : (f.left ≫ pullback.fst h b) ≫ h = T.hom ≫ b := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hfw]
    have hg : (g.left ≫ pullback.fst h b) ≫ h = T.hom ≫ b := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hgw]
    have hfgp : (f.left ≫ pullback.fst h b) ≫ h =
        (g.left ≫ pullback.fst h b) ≫ h := hf.trans hg.symm
    have hpair :
        pullback.lift f.left g.left (f.w.trans g.w.symm) ≫
          (Functor.LaxMonoidal.μ (Over.pullback b) (Over.mk h) (Over.mk h)).left ≫
          pullback.fst (pullback.fst h h ≫ h) b =
        pullback.lift (f.left ≫ pullback.fst h b) (g.left ≫ pullback.fst h b) hfgp := by
      apply pullback.hom_ext
      · simp only [Category.assoc, Over.μ_pullback_left_fst_fst', Over.pullback_obj_hom,
          Over.mk_hom]
        rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · simp only [Category.assoc, Over.μ_pullback_left_fst_snd', Over.pullback_obj_hom,
          Over.mk_hom]
        rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]
    have hmap : ((Over.pullback b).map (μ[Over.mk h])).left ≫ pullback.fst h b =
        pullback.fst (pullback.fst h h ≫ h) b ≫ (μ[Over.mk h]).left := by
      simp only [Over.pullback_map_left, Over.tensorObj_hom, Over.mk_hom, pullback.lift_fst]
    simp only [Category.assoc]
    rw [hmap]
    simpa [Category.assoc, Over.tensorObj_hom] using
      congrArg (fun q => q ≫ (μ[Over.mk h]).left) hpair

end CategoryTheory.Over

namespace AlgebraicGeometry

/-- The group-valued points of the base change are the points of the integral general linear
group over the base-changed scheme. -/
noncomputable def pullbackYonedaGrpIso (n : ℕ) (S : Scheme.{u}) :
    yonedaGrpObj (generalLinearBaseChange n S) ≅
      (Over.map (specULiftZIsTerminal.from S)).op ⋙
        yonedaGrpObj (Over.mk (generalLinearStructureMorphism.{u} n)) := by
  refine NatIso.ofComponents (fun T =>
      (CategoryTheory.Over.pullbackPointsMulEquiv (T := T.unop)
        (b := specULiftZIsTerminal.from S)
        (h := generalLinearStructureMorphism.{u} n)).toGrpIso) ?_
  intro X Y f
  ext g
  apply Over.OverMorphism.ext
  dsimp [CategoryTheory.Over.pullbackPointsMulEquiv, MulEquiv.toGrpIso, GrpCat.ofHom]
  exact Category.assoc f.unop.left g.left
    (pullback.fst (generalLinearStructureMorphism.{u} n) (specULiftZIsTerminal.from S))

/-- The group-valued points of the base-changed scheme are invertible matrices over global
sections, naturally in the scheme over `S`. -/
@[stacks 022W "base_change", sga "3 I 4.5" "GL_n representability"]
noncomputable def baseChangeGroupPointsIso (n : ℕ) (S : Scheme.{u}) :
    yonedaGrpObj (generalLinearBaseChange n S) ≅ generalLinearGroupOverFunctor n S := by
  letI : GrpObj (Over.mk (generalLinearStructureMorphism.{u} n)) :=
    generalLinearSchemeGrpObj n
  exact (pullbackYonedaGrpIso n S) ≪≫ Functor.isoWhiskerLeft
    (Over.map (specULiftZIsTerminal.from S)).op
    (yonedaGrpObjIsoOfRepresentableBy
      (Over.mk (generalLinearStructureMorphism.{u} n))
      ((Over.forget (Spec (.of (ULift.{u} ℤ)))).op ⋙ generalLinearGroupFunctor n)
      (generalLinearOverRepresentableBy n))

/-- The canonical comparison sends an `S`-point to the invertible matrix obtained by pulling
back the generic coordinates from the integral general linear scheme. -/
@[stacks 022W "base_change"]
theorem baseChangeGroupPointsIso_hom_app (n : ℕ) (S : Scheme.{u})
    (T : (Over S)ᵒᵖ) (f : T.unop ⟶ generalLinearBaseChange n S) (i j : Fin n) :
    ((baseChangeGroupPointsIso n S).hom.app T f).val i j =
      (Scheme.Γ.map
        (f.left ≫ pullback.fst (generalLinearStructureMorphism.{u} n)
          (specULiftZIsTerminal.from S)).op).hom (generalLinearCoordinateSection n i j) := by
  let e := yonedaGrpObjIsoOfRepresentableBy
    (Over.mk (generalLinearStructureMorphism.{u} n))
    ((Over.forget (Spec (.of (ULift.{u} ℤ)))).op ⋙ generalLinearGroupFunctor n)
    (generalLinearOverRepresentableBy n)
  let q := CategoryTheory.Over.pullbackPointsMulEquiv (T := T.unop)
    (b := specULiftZIsTerminal.from S) (h := generalLinearStructureMorphism.{u} n) f
  change ((e.hom.app (Opposite.op ((Over.map
      (specULiftZIsTerminal.from S)).obj T.unop)) q).val i j) = _
  dsimp [e, yonedaGrpObjIsoOfRepresentableBy, generalLinearOverRepresentableBy,
    generalLinearRepresentableBy, generalLinearGroupFunctor]
  exact (generalLinearOfLocalizedPolynomialHom_entry n _ _ i j).trans
    (schemeHomRingHomEquiv_coordinate n
      (f.left ≫ pullback.fst (generalLinearStructureMorphism.{u} n)
        (specULiftZIsTerminal.from S)) i j)

end AlgebraicGeometry
