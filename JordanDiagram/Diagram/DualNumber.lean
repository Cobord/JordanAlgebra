module

public import JordanDiagram.Diagram.Functor
public import JordanDiagram.Algebra.DualNumber

/-!
# The Lie algebra of the diagram group via dual numbers

For a diagram `G` over a commutative ring `T`, a compatible derivation `D ∈ g_G(T)` and `e ∈ T`
with `e² = 0`, the family `(1 + e Dᵢ)` is a diagram automorphism (`sqZeroAutGroup`). These satisfy
`(1 + e D)(1 + e D') = 1 + e (D + D')` and, for `e² = e'² = 0`, the commutator of `1 + e D` and
`1 + e' D'` is `1 + e e' [D, D']` (`sqZeroAutGroup_commutator`); taking `T = S[ε, ε']` recovers the
bracket of `g_F(S)` from the group functor.

For a diagram `F` over `R` (with `2` invertible) and a commutative `R`-algebra `S`,
`dualAutEquiv` identifies `g_F(S)` with the kernel of the reduction `G_F(S[ε]) → G_F(S)`,
`ε ↦ 0`, via `D ↦ 1 + ε D`, as abelian groups: the Lie algebra of the group functor `G_F` is the
compatible-derivation functor `g_F`.
-/

@[expose] public section

universe u u' v w w'

open CategoryTheory JordanAlgebra JordanAlgebra.BaseChange DualNumber TensorProduct

namespace JordanDiagram

variable {I : Type w} [Category.{w'} I]

section SquareZero

variable {T : Type u} [CommRing T] (G : JordanDiagram.{u, v} T I)

/-- The diagram automorphism `1 + e D = (1 + e Dᵢ)ᵢ`, for `e² = 0` and a compatible derivation
`D`. -/
def sqZeroAutGroup (e : T) (he : e * e = 0) (D : G.derAlgebra) : G.autGroup :=
  ⟨fun i => sqZeroAut e he (D.1 i), fun α x => by
    rw [sqZeroAut_apply, sqZeroAut_apply, D.2 α x, map_add, map_smul]⟩

variable {G}

@[simp]
theorem sqZeroAutGroup_apply (e : T) (he : e * e = 0) (D : G.derAlgebra) (i : I) (x : G.obj i) :
    (sqZeroAutGroup G e he D).1 i x = x + e • D.1 i x := rfl

/-- `(1 + e D)(1 + e D') = 1 + e (D + D')`. -/
theorem sqZeroAutGroup_add (e : T) (he : e * e = 0) (D D' : G.derAlgebra) :
    sqZeroAutGroup G e he (D + D') = sqZeroAutGroup G e he D * sqZeroAutGroup G e he D' :=
  Subtype.ext (funext fun i => sqZeroAut_add e he (D.1 i) (D'.1 i))

/-- **Commutators**: for `e² = e'² = 0` the group commutator of `1 + e D` and `1 + e' D'` is
`1 + e e' [D, D']`. -/
theorem sqZeroAutGroup_commutator (e e' : T) (he : e * e = 0) (he' : e' * e' = 0)
    (D D' : G.derAlgebra) :
    sqZeroAutGroup G e he D * sqZeroAutGroup G e' he' D' * (sqZeroAutGroup G e he D)⁻¹ *
        (sqZeroAutGroup G e' he' D')⁻¹ =
      sqZeroAutGroup G (e * e') (by rw [mul_mul_mul_comm, he, zero_mul]) ⁅D, D'⁆ :=
  Subtype.ext (funext fun i => sqZeroAut_commutator e e' he he' (D.1 i) (D'.1 i))

end SquareZero

section Dual

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (F : JordanDiagram.{u, v} R I)
variable (S : Type u') [CommRing S] [Algebra R S]

variable {F S} in
theorem mapAut_fstS_of_mem_ker {g : (F.baseChange (DualNumber S)).autGroup}
    (hg : g ∈ (autMap F (fstS R S)).ker) (i : I) : mapAut (fstS R S) (g.1 i) = 1 :=
  congrArg (fun k : (F.baseChange S).autGroup => k.1 i) hg

/-- `1 + ε D` lies in the kernel of the reduction `G_F(S[ε]) → G_F(S)`. -/
theorem sqZeroAutGroup_mem_ker (D : (F.baseChange S).derAlgebra) :
    sqZeroAutGroup _ (ε : DualNumber S) eps_mul_eps (derMap F (inlS R S) D) ∈
      (autMap F (fstS R S)).ker :=
  Subtype.ext (funext fun i => mapAut_fstS_sqZeroAut (D.1 i))

variable {F S} in
/-- The compatible derivation `D` with `g = 1 + ε D`, for `g` in the kernel of the reduction. -/
noncomputable def derOfKer (g : (autMap F (fstS R S)).ker) : (F.baseChange S).derAlgebra :=
  ⟨fun i => derOfDual (g.1.1 i) (mapAut_fstS_of_mem_ker g.2 i),
    fun α x => derOfDual_comm (F.map α) _ _ _ _ (autGroup_naturality g.1 α) x⟩

variable {F S} in
theorem sqZeroAutGroup_derOfKer (g : (autMap F (fstS R S)).ker) :
    sqZeroAutGroup _ (ε : DualNumber S) eps_mul_eps (derMap F (inlS R S) (derOfKer g)) = g.1 :=
  Subtype.ext (funext fun i => sqZeroAut_derOfDual (g.1.1 i) (mapAut_fstS_of_mem_ker g.2 i))

variable {F S} in
theorem derOfKer_sqZeroAutGroup (D : (F.baseChange S).derAlgebra) :
    derOfKer ⟨_, sqZeroAutGroup_mem_ker F S D⟩ = D :=
  Subtype.ext (funext fun i => derOfDual_sqZeroAut (D.1 i))

/-- **The Lie algebra of `G_F`**: `D ↦ 1 + ε D` is an isomorphism of abelian groups from `g_F(S)`
onto the kernel of the reduction `G_F(S[ε]) → G_F(S)`, `ε ↦ 0`. -/
noncomputable def dualAutEquiv :
    (F.baseChange S).derAlgebra ≃+ Additive (autMap F (fstS R S)).ker where
  toFun D := Additive.ofMul ⟨_, sqZeroAutGroup_mem_ker F S D⟩
  invFun g := derOfKer g.toMul
  left_inv D := derOfKer_sqZeroAutGroup D
  right_inv g := congrArg Additive.ofMul (Subtype.ext (sqZeroAutGroup_derOfKer g.toMul))
  map_add' D D' := congrArg Additive.ofMul (Subtype.ext
    ((congrArg (sqZeroAutGroup _ (ε : DualNumber S) eps_mul_eps)
      (map_add (derMap F (inlS R S)) D D')).trans (sqZeroAutGroup_add _ _ _ _)))

theorem dualAutEquiv_apply (D : (F.baseChange S).derAlgebra) (i : I)
    (x : DualNumber S ⊗[R] F.obj i) :
    (dualAutEquiv F S D).toMul.1.1 i x = x + (ε : DualNumber S) • (derMap F (inlS R S) D).1 i x :=
  rfl

end Dual

end JordanDiagram
