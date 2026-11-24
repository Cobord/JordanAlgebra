module

public import JordanDiagram.Diagram.Group
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# A lattice at the terminal node

Let `F` be a diagram and `L ⊆ J = F(+)` an additive subgroup, for instance a `ℤ`-lattice in
`J_{Z[1/2]}`. Put `Lᵢ = νᵢ⁻¹(L)` (`nodeLattice`), so `L₊ = L` (`nodeLattice_top`).

* `image_top_eq_iff`: **integral points of the whole diagram are determined at the terminal
  node**: a diagram automorphism satisfies `g₊(L) = L` exactly when `gᵢ(Lᵢ) = Lᵢ` for every `i`.
* `exists_pow_smul_mem_nodeLattice`: if every element of `J` has a multiple `cᵏ x ∈ L` (as for
  `L ⊗ Z[1/2] = J` with `c = 2`), the same holds for each `Lᵢ` in `F(i)`.
* `finite_nodeLattice`: if `L` is a finitely generated abelian group and `νᵢ` is injective, then
  `Lᵢ` is finitely generated.
-/

@[expose] public section

universe u v w w'

open CategoryTheory TerminallyPointed JordanAlgebra

namespace JordanDiagram

variable {R : Type u} [CommRing R] {I : Type w} [Category.{w'} I] [TerminallyPointed I]
variable (F : JordanDiagram.{u, v} R I) (L : AddSubgroup F.J)

/-- The node lattice `Lᵢ = νᵢ⁻¹(L)`. -/
def nodeLattice (i : I) : AddSubgroup (F.obj i) := L.comap (F.ν i : F.obj i →+ F.J)

variable {F L}

theorem mem_nodeLattice {i : I} {x : F.obj i} : x ∈ nodeLattice F L i ↔ F.ν i x ∈ L := Iff.rfl

theorem nodeLattice_top : nodeLattice F L top = L := by
  ext x
  rw [mem_nodeLattice, F.ν_top]

/-- **A lattice at the terminal node determines the integral points**: a diagram automorphism
preserves `L` at the terminal node exactly when it preserves every node lattice `Lᵢ`. -/
theorem image_top_eq_iff (g : F.autGroup) :
    g.1 top '' (L : Set F.J) = L ↔
      ∀ i, g.1 i '' (nodeLattice F L i : Set (F.obj i)) = nodeLattice F L i := by
  simp only [jordanAut.image_eq_self_iff]
  constructor
  · intro h i x
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_nodeLattice, mem_nodeLattice, ← ev_ν, ev_apply]
    exact h (F.ν i x)
  · intro h y
    have := h top y
    rwa [SetLike.mem_coe, SetLike.mem_coe, nodeLattice_top] at this

/-- If every element of `J` has a multiple `cᵏ y` in `L`, every element of `F(i)` has a multiple
`cᵏ x` in `Lᵢ`. -/
theorem exists_pow_smul_mem_nodeLattice {c : ℕ} (hL : ∀ y : F.J, ∃ k : ℕ, (c ^ k) • y ∈ L)
    (i : I) (x : F.obj i) : ∃ k : ℕ, (c ^ k) • x ∈ nodeLattice F L i := by
  obtain ⟨k, hk⟩ := hL (F.ν i x)
  exact ⟨k, by rw [mem_nodeLattice, map_nsmul]; exact hk⟩

/-- If `L` is finitely generated and `νᵢ` is injective, then `Lᵢ` is finitely generated. -/
theorem finite_nodeLattice [Module.Finite ℤ L] {i : I} (hν : Function.Injective (F.ν i)) :
    Module.Finite ℤ (nodeLattice F L i) := by
  have _ : IsNoetherian ℤ L := isNoetherian_of_isNoetherianRing_of_finite ℤ L
  let f : nodeLattice F L i →ₗ[ℤ] L :=
    { toFun := fun x => ⟨F.ν i x, x.2⟩
      map_add' := fun x y => Subtype.ext (map_add (F.ν i) (x : F.obj i) y)
      map_smul' := fun r x => Subtype.ext (map_zsmul (F.ν i : F.obj i →+ F.J) r (x : F.obj i)) }
  exact Module.Finite.of_injective f fun x y hxy =>
    Subtype.ext (hν (congrArg Subtype.val hxy))

end JordanDiagram
