module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The dyadic base ring `Z[1/2]`

`ZHalf := Localization.Away (2 : ℤ)`, the ring `Z[1/2]`.

* `zHalf_ringHom_subsingleton`: a unital map `Z[1/2] → R` is unique when it exists, and
  `nonempty_zHalf_ringHom_iff`: it exists exactly when `2` is a unit in `R`.
* So a `Z[1/2]`-algebra is the same as a commutative ring in which `2` is invertible, and every ring
  homomorphism between `Z[1/2]`-algebras commutes with the structure maps (`comp_algebraMap_zHalf`,
  `zHalfAlgHomEquiv`): `CAlg_{Z[1/2]}` is the full subcategory of commutative rings in which `2`
  is invertible.
-/

@[expose] public section

noncomputable section

/-- The ring `Z[1/2]`. -/
abbrev ZHalf : Type := Localization.Away (2 : ℤ)

/-- **A unital map `Z[1/2] → R` is unique.** -/
instance zHalf_ringHom_subsingleton (R : Type*) [Semiring R] : Subsingleton (ZHalf →+* R) :=
  ⟨fun _ _ => IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ)) (RingHom.ext_int _ _)⟩

/-- A unital map `Z[1/2] → R` exists exactly when `2` is a unit in `R`. -/
theorem nonempty_zHalf_ringHom_iff (R : Type*) [CommRing R] :
    Nonempty (ZHalf →+* R) ↔ IsUnit (2 : R) := by
  constructor
  · rintro ⟨f⟩
    have := (IsLocalization.Away.algebraMap_isUnit (2 : ℤ) (S := ZHalf)).map f
    rwa [map_ofNat, map_ofNat] at this
  · intro h
    exact ⟨IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom R) (by simpa using h)⟩

/-- Every ring homomorphism between `Z[1/2]`-algebras commutes with the structure maps. -/
theorem comp_algebraMap_zHalf {R S : Type*} [CommRing R] [CommRing S] [Algebra ZHalf R]
    [Algebra ZHalf S] (φ : R →+* S) : φ.comp (algebraMap ZHalf R) = algebraMap ZHalf S :=
  Subsingleton.elim _ _

/-- **`CAlg_{Z[1/2]}` is a full subcategory of commutative rings**: `Z[1/2]`-algebra maps are the
ring maps. -/
def zHalfAlgHomEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra ZHalf R]
    [Algebra ZHalf S] : (R →ₐ[ZHalf] S) ≃ (R →+* S) where
  toFun f := f.toRingHom
  invFun φ := { φ with commutes' := fun r => RingHom.congr_fun (comp_algebraMap_zHalf φ) r }
  left_inv _ := rfl
  right_inv _ := rfl
