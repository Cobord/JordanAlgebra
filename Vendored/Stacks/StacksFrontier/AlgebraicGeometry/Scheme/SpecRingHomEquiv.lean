module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Morphisms to an affine scheme as ring homomorphisms out of its coordinate ring

For a commutative ring `R` and a scheme `X`, the morphisms `X ⟶ Spec R` are exactly the ring
homomorphisms `R →+* Γ(X, 𝒪_X)`, compatibly with precomposition of morphisms of schemes. This
is the `Γ`-`Spec` adjunction with the opposite-category and bundling bookkeeping discharged, in
the unbundled form that the functor-of-points descriptions of affine group schemes use.

## Main definitions

* `AlgebraicGeometry.specRingHomEquiv`: the bijection itself.

## Main results

* `AlgebraicGeometry.specRingHomEquiv_comp`: precomposing with `f : X ⟶ Y` corresponds to
  postcomposing with the induced map on global sections, so the bijection is natural in `X`.
* `AlgebraicGeometry.specRingHomEquiv_id` and `AlgebraicGeometry.specRingHomEquiv_specMap`
  evaluate it on the identity of an affine scheme and on the spectrum of a ring map.

## Implementation notes

`AlgebraicGeometry.schemeHomRingHomEquiv` of
`StacksFrontier/AlgebraicGeometry/GroupScheme/Examples/GeneralLinear.lean` is this bijection at the
coordinate ring of `GL_n`; it is defined there as a special case of this one, so there is a
single proof of the adjunction bookkeeping.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Morphisms from a scheme to the spectrum of a commutative ring are exactly the ring
homomorphisms from that ring to the ring of global sections. -/
noncomputable def specRingHomEquiv (R : Type u) [CommRing R] (X : Scheme.{u}) :
    (X ⟶ Spec (CommRingCat.of R)) ≃ (R →+* Scheme.Γ.obj (op X)) where
  toFun f :=
    CommRingCat.Hom.hom
      ((ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R))).symm f).unop
  invFun f :=
    ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R)) (CommRingCat.ofHom f).op
  left_inv f := (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R))).apply_symm_apply f
  right_inv f := by
    ext x
    exact congrArg (fun q : CommRingCat.of R ⟶ Scheme.Γ.obj (op X) => q.hom x)
      (congrArg Opposite.unop
        ((ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R))).symm_apply_apply
          (CommRingCat.ofHom f).op))

/-- `AlgebraicGeometry.specRingHomEquiv` unfolded to the inverse of the adjunction bijection. -/
private theorem specRingHomEquiv_eq (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    specRingHomEquiv R X f =
      ((ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R))).symm f).unop.hom := rfl

/-- `AlgebraicGeometry.specRingHomEquiv` is natural in the scheme: precomposing a morphism to
`Spec R` with `f : X ⟶ Y` corresponds to postcomposing the ring homomorphism with the map
induced by `f` on global sections. -/
theorem specRingHomEquiv_comp (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of R)) :
    specRingHomEquiv R X (f ≫ g) =
      (Scheme.Γ.map f.op).hom.comp (specRingHomEquiv R Y g) := by
  rw [specRingHomEquiv_eq, specRingHomEquiv_eq, ΓSpec.adjunction.homEquiv_naturality_left_symm]
  rfl

/-- `AlgebraicGeometry.specRingHomEquiv` sends the identity of an affine scheme to the inverse
of the global-sections isomorphism. -/
theorem specRingHomEquiv_id (R : Type u) [CommRing R] :
    specRingHomEquiv R (Spec (CommRingCat.of R)) (𝟙 (Spec (CommRingCat.of R))) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  let X := Spec (CommRingCat.of R)
  let e := ΓSpec.adjunction.homEquiv X (op (CommRingCat.of R))
  rw [specRingHomEquiv_eq]
  have he : e ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.op) = (𝟙 X : X ⟶ X) := by
    dsimp only [e, X]
    apply ext_to_Spec
    simpa [X] using
      (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        (X := Spec (CommRingCat.of R)) (B := CommRingCat.of R)
        (φ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
  rw [e.symm_apply_eq.2 he.symm]
  rfl

/-- `AlgebraicGeometry.specRingHomEquiv` sends the spectrum of a ring homomorphism to that
homomorphism, followed by the global-sections isomorphism of the target. -/
theorem specRingHomEquiv_specMap (R : Type u) [CommRing R] {B : Type u} [CommRing B]
    (φ : R →+* B) :
    specRingHomEquiv R (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom φ)) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.comp φ := by
  rw [← Category.comp_id (Spec.map (CommRingCat.ofHom φ)), specRingHomEquiv_comp,
    specRingHomEquiv_id]
  ext x
  exact congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).hom x).symm

end AlgebraicGeometry

end
