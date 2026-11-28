module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Group

/-!
# Class sums over double cosets

For a group `G` with subgroups `Γ` and `K`, the stabilizer of the class `Γ g K` is
`Γ ∩ g K g⁻¹` (`DoubleCoset.classAut`), and its order depends only on the double coset
(`DoubleCoset.card_classAut_mul_mul`). The class sum of `f : G → ℚ` is the sum over `Γ \ G / K` of
`f(g) / #(Γ ∩ g K g⁻¹)` (`DoubleCoset.classSum`), and the mass is the class sum of `1`
(`DoubleCoset.mass`). For `f` left invariant under `Γ` and right invariant under `K`, any system
of representatives computes it (`DoubleCoset.classSum_eq_of_rep`).

An infinite stabilizer contributes `0`, as `Nat.card` of an infinite type is `0`.

## Source

The definitions and the invariance argument follow `New.classAut`, `New.classSum`,
`New.card_classAut_mul_mul` and `New.classSum_eq_finsum_of_rep` in `grh/src/Lib/Adelic/Hecke/Basic.lean`
of the Lean 4 formalization of GRH for Dirichlet L-functions, https://github.com/lsernau/grh-lean
(Apache 2.0). Here they are restated with rational values.
-/

@[expose] public section

namespace DoubleCoset

variable {G : Type*} [Group G] (Γ K : Subgroup G)

/-- The stabilizer `Γ ∩ g K g⁻¹` of the class `Γ g K`. -/
def classAut (g : G) : Subgroup G where
  carrier := {δ | δ ∈ Γ ∧ g⁻¹ * δ * g ∈ K}
  one_mem' := ⟨Γ.one_mem, by simp⟩
  mul_mem' {a b} ha hb := ⟨Γ.mul_mem ha.1 hb.1, by
    convert K.mul_mem ha.2 hb.2 using 1
    group⟩
  inv_mem' {a} ha := ⟨Γ.inv_mem ha.1, by
    convert K.inv_mem ha.2 using 1
    group⟩

variable {Γ K}

theorem mem_classAut {g δ : G} : δ ∈ classAut Γ K g ↔ δ ∈ Γ ∧ g⁻¹ * δ * g ∈ K := Iff.rfl

/-- The order of the stabilizer depends only on the double coset. -/
theorem card_classAut_mul_mul {γ k : G} (hγ : γ ∈ Γ) (hk : k ∈ K) (g : G) :
    Nat.card (classAut Γ K (γ * g * k)) = Nat.card (classAut Γ K g) := by
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ => ?_)
  change δ ∈ classAut Γ K (γ * g * k) ↔ γ⁻¹ * δ * γ⁻¹⁻¹ ∈ classAut Γ K g
  rw [inv_inv, mem_classAut, mem_classAut, mul_mem_cancel_right hγ, mul_mem_cancel_left (inv_mem hγ)]
  have h : (γ * g * k)⁻¹ * δ * (γ * g * k) = k⁻¹ * (g⁻¹ * (γ⁻¹ * δ * γ) * g) * k := by group
  rw [h, mul_mem_cancel_right hk, mul_mem_cancel_left (inv_mem hk)]

theorem card_classAut_of_mk_eq {g g' : G} (h : mk Γ K g = mk Γ K g') :
    Nat.card (classAut Γ K g) = Nat.card (classAut Γ K g') := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := eq.1 h
  exact (card_classAut_mul_mul hγ hk g).symm

variable (Γ K)

/-- The class sum `∑_{Γ g K} f(g) / #(Γ ∩ g K g⁻¹)`, with chosen representatives. -/
noncomputable def classSum (f : G → ℚ) : ℚ :=
  ∑ᶠ c : Quotient (Γ : Set G) K, (Nat.card (classAut Γ K c.out) : ℚ)⁻¹ * f c.out

/-- The mass `∑_{Γ g K} 1 / #(Γ ∩ g K g⁻¹)`. -/
noncomputable def mass : ℚ := classSum Γ K 1

variable {Γ K}

/-- For `f` left invariant under `Γ` and right invariant under `K`, the class sum can be computed
with any system of representatives. -/
theorem classSum_eq_of_rep {f : G → ℚ} (hf_left : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (hf_right : ∀ k ∈ K, ∀ g, f (g * k) = f g) (r : Quotient (Γ : Set G) K → G)
    (hr : ∀ c, mk Γ K (r c) = c) :
    classSum Γ K f = ∑ᶠ c, (Nat.card (classAut Γ K (r c)) : ℚ)⁻¹ * f (r c) := by
  refine finsum_congr fun c => ?_
  have hc : mk Γ K (r c) = mk Γ K c.out := (hr c).trans (out_eq' c).symm
  obtain ⟨γ, hγ, k, hk, hout⟩ := eq.1 hc
  rw [hout, card_classAut_mul_mul hγ hk, hf_right k hk, hf_left γ hγ]

end DoubleCoset
