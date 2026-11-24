module

public import Jordan.JordanAlgebra
public import Jordan.StructureAlgebra
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.Module

@[expose] public section

/-- A (linear) Jordan triple system: an `R`-module `M` equipped with a triple product
`{x, y, z}`, bundled as a tri"linear" (antilinear in the second argument) map
`M →ₗ[R] M →ₛₗ[starRingEnd R] M →ₗ[R] M`
(so (anti)linearity in each argument is from the type),
symmetric in its outer arguments (`triple_comm`),
and satisfying the
Jordan triple identity relating the "box operators"
`L(x, y) z = triple x y z`:

  `{x, y, {u, v, w}} - {u, v, {x, y, w}}` =
  `{{x, y, u}, v, w} - {u, {y, x, v}, w}`

that is, `[L(x, y), L(u, v)] = L(L(x, y) u, v) - L(u, L(y, x) v)`.

The last term is `{u, {y, x, v}, w}` and not `{u, {v, y, x}, w}`: the inner triple sits in the
antilinear middle slot, so every term must be linear in `x`, `u`, `w` and antilinear in `y`, `v`,
like the left-hand side; `{y, x, v}` there has that pattern, `{v, y, x}` would be linear in `y`
and antilinear in `x`.
-/
class JordanTriple (R : outParam (Type u)) (M : Type v) [CommRing R] [StarRing R] extends
    AddCommGroup M, Module R M where
  triple : M →ₗ[R] M →ₛₗ[starRingEnd R] M →ₗ[R] M
  triple_comm : ∀ x y z, triple x y z = triple z y x
  triple_identity : ∀ x y u v w,
      triple x y (triple u v w) - triple u v (triple x y w) =
        triple (triple x y u) v w - triple u (triple y x v) w

namespace JordanAlgebra

section BoxOperator

/-! ### The box operator `V_{a,b} = L_{ab} + [L_a, L_b]`

On any Jordan algebra (no involution needed), the box operator satisfies the operator identity
`[V_{x,y}, V_{u,v}] = V_{V_{x,y} u, v} - V_{u, V_{y,x} v}` (`box_commutator`), proved from two
facts, with `D = [L_x, L_y]` so that `V_{x,y} = L_{xy} + D`:

* `lmul_commutator_box`: `[L_a, V_{u,v}] = V_{au,v} - V_{u,av}`, from the linearized fundamental
  formula `lmul_mul_mul_eq` (twice) and the linearized Jordan identity
  `lie_lmul_lmul_add_add_eq_zero`;
* `derivation_commutator_box`: `D` is a derivation (`JordanDerivation.inner`), so
  `[D, V_{u,v}] = V_{Du,v} + V_{u,Dv}`.
-/

variable {R M : Type*} [CommRing R] [JordanAlgebra R M]

local notation "L" => AddMonoid.End.mulLeft

/-- Pointwise form of `lmul_mul_mul_eq`, applied at `z`: expands `(b * d) * c * z` as a
combination of `M`-products rather than of composed endomorphisms. -/
theorem mul_mul_eq [Invertible (2 : R)] (b c d z : M) :
    (b * d) * c * z = (b * d) * (c * z) + (c * d) * (b * z) + (b * c) * (d * z)
      - b * (c * (d * z)) - d * (c * (b * z)) :=
  congrArg (fun f : AddMonoid.End M => f z) (lmul_mul_mul_eq (R := R) b c d)

/-- The box operator `V_{a,b} = L_{ab} + [L_a, L_b]` on a Jordan algebra. -/
def box (a b : M) : AddMonoid.End M := L (a * b) + (L a * L b - L b * L a)

theorem box_apply (a b z : M) : box a b z = (a * b) * z + (a * (b * z) - b * (a * z)) := rfl

theorem box_add_left (a a' b : M) : box (a + a') b = box a b + box a' b := by
  simp only [box, add_mul, map_add]
  noncomm_ring

theorem box_add_right (a b b' : M) : box a (b + b') = box a b + box a b' := by
  simp only [box, mul_add, map_add]
  noncomm_ring

theorem box_neg_right (a b : M) : box a (-b) = -box a b := by
  simp only [box, mul_neg, map_neg]
  noncomm_ring

theorem box_sub_right (a b b' : M) : box a (b - b') = box a b - box a b' := by
  rw [sub_eq_add_neg, box_add_right, box_neg_right, ← sub_eq_add_neg]

attribute [local instance] LieRing.ofAssociativeRing in
/-- `[L_a, V_{u,v}] = V_{au,v} - V_{u,av}`. -/
theorem lmul_commutator_box [Invertible (2 : R)] (a u v : M) :
    L a * box u v - box u v * L a = box (a * u) v - box u (a * v) := by
  have hlin := lie_lmul_lmul_add_add_eq_zero (R := R) a u v
  simp only [Ring.lie_def] at hlin
  have h1 := lmul_mul_mul_eq (R := R) a v u
  have h2 := lmul_mul_mul_eq (R := R) a u v
  rw [jordan_mul_comm v a] at hlin
  rw [jordan_mul_comm v u] at h1
  simp only [box]
  rw [jordan_mul_comm u (a * v), h1, h2]
  rw [← sub_eq_zero]
  rw [← hlin]
  noncomm_ring

/-- A derivation as an additive endomorphism, to compose with the operators `L a`. -/
def derEnd (D : JordanDerivation R M) : AddMonoid.End M := (D : M →ₗ[R] M).toAddMonoidHom

theorem derEnd_apply (D : JordanDerivation R M) (z : M) : derEnd D z = D z := rfl

/-- A derivation `D` satisfies `[D, L_a] = L_{Da}`. -/
theorem derivation_commutator_lmul (D : JordanDerivation R M) (a : M) :
    derEnd D * L a - L a * derEnd D = L (D a) :=
  AddMonoidHom.ext fun z => by
    change D (a * z) - a * D z = D a * z
    rw [JordanDerivation.leibniz]
    abel

/-- A derivation `D` satisfies `[D, V_{u,v}] = V_{Du,v} + V_{u,Dv}`. -/
theorem derivation_commutator_box (D : JordanDerivation R M) (u v : M) :
    derEnd D * box u v - box u v * derEnd D = box (D u) v + box u (D v) := by
  have hu := derivation_commutator_lmul D u
  have hv := derivation_commutator_lmul D v
  have huv := derivation_commutator_lmul D (u * v)
  rw [JordanDerivation.leibniz, map_add] at huv
  simp only [box]
  rw [← sub_eq_zero]
  calc _ = (derEnd D * L (u * v) - L (u * v) * derEnd D - (L (u * D v) + L (D u * v)))
        + ((derEnd D * L u - L u * derEnd D - L (D u)) * L v
          + L u * (derEnd D * L v - L v * derEnd D - L (D v)))
        - ((derEnd D * L v - L v * derEnd D - L (D v)) * L u
          + L v * (derEnd D * L u - L u * derEnd D - L (D u))) := by
          noncomm_ring
    _ = 0 := by rw [huv, hu, hv]; noncomm_ring

/-- The inner derivation `[L_x, L_y]` as an operator. -/
theorem derEnd_inner [Invertible (2 : R)] (x y : M) :
    derEnd (JordanDerivation.inner (R := R) x y) = L x * L y - L y * L x :=
  AddMonoidHom.ext fun _ => rfl

/-- **The Jordan triple identity for the box operator**:
`[V_{x,y}, V_{u,v}] = V_{V_{x,y} u, v} - V_{u, V_{y,x} v}`. -/
theorem box_commutator [Invertible (2 : R)] (x y u v : M) :
    box x y * box u v - box u v * box x y = box (box x y u) v - box u (box y x v) := by
  set D := JordanDerivation.inner (R := R) x y
  have hD := derivation_commutator_box D u v
  rw [derEnd_inner] at hD
  have hL := lmul_commutator_box (R := R) (x * y) u v
  have hxu : box x y u = (x * y) * u + D u := rfl
  have hyv : box y x v = (x * y) * v - D v := by
    rw [box_apply, jordan_mul_comm y x]
    change _ = _ - (x * (y * v) - y * (x * v))
    abel
  rw [hxu, hyv, box_add_left, box_sub_right]
  have hbox : box x y = L (x * y) + (L x * L y - L y * L x) := rfl
  rw [hbox]
  calc _ = (L (x * y) * box u v - box u v * L (x * y)) +
        ((L x * L y - L y * L x) * box u v - box u v * (L x * L y - L y * L x)) := by
          noncomm_ring
    _ = _ := by rw [hL, hD]; abel

end BoxOperator

section TripleProduct

/-! ### The triple product of a Jordan algebra with involution

For a Jordan algebra `M` with an involution `*` (`StarRing M`, compatible with the scalars'
involution via `StarModule R M`), the triple product is
`{x, y, z} = (x * y*) * z + (z * y*) * x - (x * z) * y*`. It is linear in `x` and `z` and
antilinear in `y`, and equals `V_{x, y*} z` (`tripleProduct_eq_box`). The trivial involution on
`M` and on `R` gives the real case `{x, y, z} = (x * y) * z + (z * y) * x - (x * z) * y`.
-/

variable {R M : Type*} [CommRing R] [StarRing R] [JordanAlgebra R M] [StarRing M]
  [StarModule R M]

/-- The Jordan triple product of a Jordan algebra with involution:
`{x, y, z} = (x * y*) * z + (z * y*) * x - (x * z) * y*`. -/
def tripleProduct (x y z : M) : M := (x * star y) * z + (z * star y) * x - (x * z) * star y

omit [StarRing R] [StarModule R M] in
theorem tripleProduct_add_left (x₁ x₂ y z : M) :
    tripleProduct (x₁ + x₂) y z = tripleProduct x₁ y z + tripleProduct x₂ y z := by
  simp only [tripleProduct, add_mul, mul_add]
  abel

omit [StarRing R] [StarModule R M] in
theorem tripleProduct_smul_left (r : R) (x y z : M) :
    tripleProduct (r • x) y z = r • tripleProduct x y z := by
  simp only [tripleProduct, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]

omit [StarRing R] [StarModule R M] in
theorem tripleProduct_add_mid (x y₁ y₂ z : M) :
    tripleProduct x (y₁ + y₂) z = tripleProduct x y₁ z + tripleProduct x y₂ z := by
  simp only [tripleProduct, star_add, mul_add, add_mul]
  abel

/-- The triple product is antilinear in its middle argument. -/
theorem tripleProduct_smul_mid (r : R) (x y z : M) :
    tripleProduct x (r • y) z = star r • tripleProduct x y z := by
  simp only [tripleProduct, star_smul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]

omit [StarRing R] [StarModule R M] in
theorem tripleProduct_add_right (x y z₁ z₂ : M) :
    tripleProduct x y (z₁ + z₂) = tripleProduct x y z₁ + tripleProduct x y z₂ := by
  simp only [tripleProduct, mul_add, add_mul]
  abel

omit [StarRing R] [StarModule R M] in
theorem tripleProduct_smul_right (r : R) (x y z : M) :
    tripleProduct x y (r • z) = r • tripleProduct x y z := by
  simp only [tripleProduct, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub]

/-- `tripleProduct`, bundled as the map, linear-antilinear-linear, required by `JordanTriple`. -/
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
        rw [LinearMap.smul_apply, starRingEnd_apply]
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

omit [StarRing R] [StarModule R M] in
/-- The triple product is symmetric in its outer arguments: `{x, y, z} = {z, y, x}`. This holds
because the underlying Jordan product is fully commutative (`jordan_mul_comm`), so it does not yet
need the Jordan identity. -/
theorem tripleProduct_comm (x y z : M) : tripleProduct x y z = tripleProduct z y x := by
  simp only [tripleProduct]
  rw [jordan_mul_comm x z]
  abel

omit [StarRing R] [StarModule R M] in
/-- The triple product is the box operator at `y*`: `{x, y, z} = V_{x, y*} z`. -/
theorem tripleProduct_eq_box (x y z : M) : tripleProduct x y z = box x (star y) z := by
  rw [box_apply, tripleProduct, jordan_mul_comm (z * star y) x, jordan_mul_comm z (star y),
    jordan_mul_comm (x * z) (star y)]
  abel

omit [StarRing R] [StarModule R M] in
/-- The involution commutes with the box operator: `(V_{a,b} z)* = V_{a*,b*} z*`. -/
theorem star_box (a b z : M) : star (box a b z) = box (star a) (star b) (star z) := by
  simp only [box_apply, star_add, star_sub, star_mul]
  rw [jordan_mul_comm (star z) (star b * star a), jordan_mul_comm (star b) (star a),
    jordan_mul_comm (star z * star b) (star a), jordan_mul_comm (star z) (star b),
    jordan_mul_comm (star z * star a) (star b), jordan_mul_comm (star z) (star a)]

/-- The Jordan triple system structure on a Jordan algebra with involution, via the triple
product `{x, y, z} = (x * y*) * z + (z * y*) * x - (x * z) * y*`. -/
instance [Invertible (2 : R)] : JordanTriple R M where
  triple := tripleLinearMap
  triple_comm := tripleProduct_comm
  triple_identity x y u v w := by
    simp only [tripleLinearMap_apply, tripleProduct_eq_box, star_box, star_star]
    exact congrArg (fun f : AddMonoid.End M => f w) (box_commutator (R := R) x (star y) u (star v))

end TripleProduct

end JordanAlgebra
