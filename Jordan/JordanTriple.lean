import Jordan.JordanAlgebra
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.LinearMap.Defs

/-- A (linear) Jordan triple system: an `R`-module `M` equipped with a triple product
`{x, y, z}`, bundled as a trilinear map `M →ₗ[R] M →ₗ[R] M →ₗ[R] M` (so linearity in each
argument is automatic), symmetric in its outer arguments (`triple_comm`), and satisfying the
Jordan triple identity relating the "box operators" `L(x, y) z = triple x y z`:

    {x, y, {u, v, w}} - {u, v, {x, y, w}} = {{x, y, u}, v, w} - {u, {v, y, x}, w} -/
class JordanTriple (R : outParam (Type u)) (M : Type v) [CommRing R] [StarRing R] extends
    AddCommGroup M, Module R M where
  triple : M →ₗ[R] M →ₛₗ[starRingEnd R] M →ₗ[R] M
  triple_comm : ∀ x y z, triple x y z = triple z y x
  triple_identity : ∀ x y u v w,
      triple x y (triple u v w) - triple u v (triple x y w) =
        triple (triple x y u) v w - triple u (triple v y x) w

namespace JordanAlgebra

variable {R M : Type*} [CommRing R] [StarRing R] [TrivialStar R] [JordanAlgebra R M]

/-- The Jordan triple product associated to a Jordan algebra:
`{x, y, z} = (x * y) * z + (z * y) * x - (x * z) * y`. -/
def tripleProduct (x y z : M) : M := (x * y) * z + (z * y) * x - (x * z) * y

omit [StarRing R] in
private theorem tripleProduct_add_left (x₁ x₂ y z : M) :
    tripleProduct (x₁ + x₂) y z = tripleProduct x₁ y z + tripleProduct x₂ y z := by
  simp only [tripleProduct, add_mul, mul_add]
  abel

omit [StarRing R] in
private theorem tripleProduct_smul_left (r : R) (x y z : M) :
    tripleProduct (r • x) y z = r • tripleProduct x y z := by
  simp only [tripleProduct, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]

omit [StarRing R] in
private theorem tripleProduct_add_mid (x y₁ y₂ z : M) :
    tripleProduct x (y₁ + y₂) z = tripleProduct x y₁ z + tripleProduct x y₂ z := by
  simp only [tripleProduct, mul_add, add_mul]
  abel

omit [StarRing R] in
private theorem tripleProduct_smul_mid (r : R) (x y z : M) :
    tripleProduct x (r • y) z = r • tripleProduct x y z := by
  simp only [tripleProduct, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]

omit [StarRing R] in
private theorem tripleProduct_add_right (x y z₁ z₂ : M) :
    tripleProduct x y (z₁ + z₂) = tripleProduct x y z₁ + tripleProduct x y z₂ := by
  simp only [tripleProduct, mul_add, add_mul]
  abel

omit [StarRing R] in
private theorem tripleProduct_smul_right (r : R) (x y z : M) :
    tripleProduct x y (r • z) = r • tripleProduct x y z := by
  simp only [tripleProduct, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]

/-- `tripleProduct`, bundled as the trilinear map required by `JordanTriple`. -/
def tripleLinearMap : M →ₗ[R] M →ₛₗ[starRingEnd R] M →ₗ[R] M where
  toFun x :=
    { toFun := fun y =>
        { toFun := tripleProduct x y
          map_add' := tripleProduct_add_right x y
          map_smul' := fun r z => by
            rw [RingHom.id_apply, tripleProduct_smul_right] }
      map_add' := fun y₁ y₂ => by
        ext z
        exact tripleProduct_add_mid x y₁ y₂ z
      map_smul' := fun r y => by
        ext z
        simp only [LinearMap.smul_apply, conj_trivial]
        exact tripleProduct_smul_mid r x y z }
  map_add' x₁ x₂ := by
    ext y z
    exact tripleProduct_add_left x₁ x₂ y z
  map_smul' r x := by
    ext y z
    rw [RingHom.id_apply]
    exact tripleProduct_smul_left r x y z

@[simp]
theorem tripleLinearMap_apply (x y z : M) : tripleLinearMap (R := R) x y z = tripleProduct x y z :=
  rfl

omit [StarRing R] in
/-- The triple product is symmetric in its outer arguments: `{x, y, z} = {z, y, x}`. This holds
because the underlying Jordan product is fully commutative (`jordan_mul_comm`), so it does not yet
need the Jordan identity. -/
theorem tripleProduct_comm (x y z : M) : tripleProduct x y z = tripleProduct z y x := by
  simp only [tripleProduct]
  rw [jordan_mul_comm x z]
  abel

omit [StarRing R] in
/-- Pointwise form of `lmul_mul_mul_eq`, applied at `z`: expands `(b * d) * c * z` as a
combination of `M`-products rather than of composed endomorphisms. This is the workhorse used to
expand triple products against an extra factor below. -/
private theorem mul_mul_eq [Invertible (2 : R)] (b c d z : M) :
    (b * d) * c * z = (b * d) * (c * z) + (c * d) * (b * z) + (b * c) * (d * z)
      - b * (c * (d * z)) - d * (c * (b * z)) :=
  congrArg (fun f : AddMonoid.End M => f z) (lmul_mul_mul_eq b c d)

omit [StarRing R] in
/-- Right-multiplying a triple product by a fourth element, fully expanded via three applications
of `mul_mul_eq` (one per term of `tripleProduct`). -/
private theorem tripleProduct_mul [Invertible (2 : R)] (a b c d : M) :
    tripleProduct a b c * d =
      (a * b) * (c * d) + (b * c) * (a * d) + (a * c) * (b * d)
        - a * (c * (b * d)) - b * (c * (a * d)) - c * (a * (b * d)) - b * (a * (c * d))
        + a * (b * (c * d)) + c * (b * (a * d)) := by
  simp only [tripleProduct, add_mul, sub_mul]
  rw [mul_mul_eq a c b d, mul_mul_eq c a b d, mul_mul_eq a b c d,
    jordan_mul_comm c b, jordan_mul_comm c a]
  abel

/-- The Jordan triple system structure on a Jordan algebra, via the triple product
`{x, y, z} = (x * y) * z + (z * y) * x - (x * z) * y`. -/
instance [Invertible (2 : R)] : JordanTriple R M where
  triple := tripleLinearMap
  triple_comm := tripleProduct_comm
  triple_identity := by
    intros x y u v w
    have term1 :
      ((tripleLinearMap x) y) (((tripleLinearMap u) v) w) =
      tripleLinearMap (tripleLinearMap u v w) y x := by
      simp
      rw [tripleProduct_comm]
    have term2 :
      ((tripleLinearMap u) v) (((tripleLinearMap x) y) w) =
      tripleLinearMap (tripleLinearMap x y w) v u := by
      simp
      rw [tripleProduct_comm]
    rw [term1, term2]
    simp
    simp only [tripleProduct]
    repeat rw [sub_mul, add_mul]
    repeat rw [mul_sub, mul_add]
    rw [jordan_mul_comm (x * y) (u * v * w), mul_mul_eq u w v (x * y)]
    abel_nf
    /- TODO: goal is now 40 raw multiplication terms (was 36 before the `mul_mul_eq` expansion
    above). `find_cancel.py lhs.txt rhs.txt --rule rule.txt --rule-line 30` (in the project root)
    shows 5 of those pairs are equal up to `jordan_mul_comm` (e.g. `(u*v)*(w*(x*y))` vs
    `(u*v)*((x*y)*w)`), but `abel_nf` can't see that on its own -- it only normalizes `+`/`-`/`•`,
    never `*`. They need explicit `rw [jordan_mul_comm ...]` calls first to actually cancel,
    which would bring the goal down to the 30 remaining forms `find_cancel.py` reports. From
    there, sweeping (`--rule-line all`) over `rule.txt`'s other 29 `mul_mul_eq` instantiations (or
    new ones for the leftover left-chained `...*y*x` terms) is the way to keep chipping away. -/
    sorry

end JordanAlgebra
