import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# The Moore determinant of a matrix over a non-commutative ring

`Matrix.det` doesn't even typecheck for `Matrix n n M` when `M` is non-commutative (e.g. `M` a
quaternion algebra). The classical fix, for a matrix over such an `M`, is the *Moore determinant*:
sum over permutations `σ` of `sgn σ` times a product, over the orbits of `σ` (read as cycles, each
ordered by starting at its largest index, the orbits themselves taken in decreasing order of their
largest index), of the cyclic product of entries along that orbit.

This is a general construction that has nothing to do with quaternions specifically: it only needs
`M` to be a ring and `n` (the index type) to carry a linear order (to make sense of "largest
index"). This file builds the formula (`mooreTerm`, and the pieces it's assembled from) and its
basic algebraic properties -- `R`-linearity of the scaling degree (`mooreTerm_smul`) and the
identity-matrix value (`mooreTerm_one`) -- for any `R`-algebra `M`. What's *not* attempted here is
the deeper classical theorem (specific to genuine quaternion algebras) that this sum is always
central; that's a separate, nontrivial fact about the formula's well-definedness on Hermitian
input, not needed for the algebraic properties above.
-/

open scoped Classical

/-! ### Orbit combinatorics

Purely about a permutation `σ` of a linearly-ordered index type `n` -- no ring `R` or algebra `M`
involved at all. -/

section Orbits

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The orbit of `i` under a permutation `σ`, as a `Finset` (always nonempty, always contains
`i` -- a fixed point gets the singleton orbit `{i}`). -/
def orbitFinset (σ : Equiv.Perm n) (i : n) : Finset n :=
  Finset.univ.filter (fun j => σ.SameCycle i j)

omit [LinearOrder n] in
theorem mem_orbitFinset_self (σ : Equiv.Perm n) (i : n) : i ∈ orbitFinset σ i := by
  simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.SameCycle.refl σ i

omit [LinearOrder n] in
theorem orbitFinset_nonempty (σ : Equiv.Perm n) (i : n) : (orbitFinset σ i).Nonempty :=
  ⟨i, mem_orbitFinset_self σ i⟩

omit [LinearOrder n] in
theorem orbitFinset_eq_of_mem (σ : Equiv.Perm n) {i j : n} (h : j ∈ orbitFinset σ i) :
    orbitFinset σ j = orbitFinset σ i := by
  simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and] at h
  ext k
  simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hk => h.trans hk, fun hk => h.symm.trans hk⟩

omit [LinearOrder n] in
theorem orbitFinset_disjoint_of_not_mem (σ : Equiv.Perm n) {i m : n} (hi : i ∉ orbitFinset σ m) :
    Disjoint (orbitFinset σ i) (orbitFinset σ m) := by
  rw [Finset.disjoint_left]
  intro j hji hjm
  simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hji hjm hi
  exact hi (hji.trans hjm.symm).symm

/-- `S` is a union of complete `σ`-orbits: every orbit met by `S` is entirely contained in `S`. -/
def IsOrbitClosed (σ : Equiv.Perm n) (S : Finset n) : Prop :=
  ∀ i ∈ S, orbitFinset σ i ⊆ S

omit [LinearOrder n] in
theorem isOrbitClosed_univ (σ : Equiv.Perm n) : IsOrbitClosed σ (Finset.univ : Finset n) :=
  fun _ _ _ _ => Finset.mem_univ _

theorem isOrbitClosed_sdiff (σ : Equiv.Perm n) {S : Finset n} (hS : IsOrbitClosed σ S)
    (h : S.Nonempty) : IsOrbitClosed σ (S \ orbitFinset σ (S.max' h)) := by
  intro i hi
  simp only [Finset.mem_sdiff] at hi
  obtain ⟨hiS, hiOrb⟩ := hi
  intro j hj
  simp only [Finset.mem_sdiff]
  refine ⟨hS i hiS hj, ?_⟩
  have hdisj := orbitFinset_disjoint_of_not_mem σ hiOrb
  exact fun hjOrb => (Finset.disjoint_left.mp hdisj hj) hjOrb

theorem sdiff_orbitFinset_card_lt (σ : Equiv.Perm n) (S : Finset n) (h : S.Nonempty) :
    (S \ orbitFinset σ (S.max' h)).card < S.card := by
  have hm : S.max' h ∈ S := S.max'_mem h
  have hmem : S.max' h ∉ S \ orbitFinset σ (S.max' h) := by
    simp [mem_orbitFinset_self]
  have hsub : S \ orbitFinset σ (S.max' h) ⊆ S := Finset.sdiff_subset
  refine Finset.card_lt_card (hsub.ssubset_of_ne (fun heq => hmem ?_))
  rw [heq]
  exact hm

/-- If `σ` moves the largest element of an orbit, it moves every element of that orbit (an orbit
of a fixed point is always the singleton orbit `{that point}`, so a nontrivial orbit -- one with
`card ≥ 2` -- can't have a fixed max). -/
theorem orbitFinset_max_moved_of_card_ge_two (σ : Equiv.Perm n) (m : n)
    (h : (orbitFinset σ m).Nonempty) (hcard : 2 ≤ (orbitFinset σ m).card) :
    σ ((orbitFinset σ m).max' h) ≠ (orbitFinset σ m).max' h := by
  set m' := (orbitFinset σ m).max' h with hm'def
  intro heq
  have hmem : m' ∈ orbitFinset σ m := (orbitFinset σ m).max'_mem h
  have horbit_eq : orbitFinset σ m' = orbitFinset σ m := orbitFinset_eq_of_mem σ hmem
  have hsingleton : orbitFinset σ m' = {m'} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨mem_orbitFinset_self σ m', fun j hj => ?_⟩
    simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hj.eq_of_left heq).symm
  rw [horbit_eq] at hsingleton
  rw [hsingleton] at hcard
  simp at hcard

/-- The orbit of a fixed point is the singleton orbit, and its (unique) max is the point itself.
-/
theorem orbitFinset_max_eq_of_fixed (σ : Equiv.Perm n) (m : n) (h : (orbitFinset σ m).Nonempty)
    (hfix : σ m = m) : (orbitFinset σ m).max' h = m := by
  have hTeq : orbitFinset σ m = {m} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨mem_orbitFinset_self σ m, fun j hj => ?_⟩
    simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hj.eq_of_left hfix).symm
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    rw [hTeq] at hy
    simp at hy
    exact le_of_eq hy
  · exact Finset.le_max' _ m (mem_orbitFinset_self σ m)

end Orbits

/-! ### The Moore-determinant formula

Needs a (not necessarily commutative) ring `M` of entries, but no scalar ring `R` yet. -/

section MooreTerm

variable {M : Type*} [Ring M]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The cyclic product of the entries of `A` along one orbit `S` of `σ`, read starting at `S`'s
largest index: for `S = {m, σ m, σ² m, ..., σ^(k-1) m}` (`m` the max, `k = S.card`), the product
`A[m][σ m] * A[σ m][σ² m] * ⋯ * A[σ^(k-1) m][m]`. For a singleton `S = {m}` (a fixed point of
`σ`), this is just `A[m][m]`. -/
def orbitProd (A : Matrix n n M) (σ : Equiv.Perm n) (S : Finset n) (h : S.Nonempty) : M :=
  ((List.range S.card).map
    (fun i => A ((σ ^ i) (S.max' h)) ((σ ^ (i + 1)) (S.max' h)))).prod

/-- The Moore-determinant term for a single permutation `σ`: peel off the orbit of the largest
remaining index, multiply its cyclic product onto the (recursively computed) product for the rest.
-/
def mooreTermAux (A : Matrix n n M) (σ : Equiv.Perm n) : (S : Finset n) → M
  | S =>
    if h : S.Nonempty then
      orbitProd A σ (orbitFinset σ (S.max' h)) (orbitFinset_nonempty σ _) *
        mooreTermAux A σ (S \ orbitFinset σ (S.max' h))
    else 1
  termination_by S => S.card
  decreasing_by exact sdiff_orbitFinset_card_lt σ S h

/-- The Moore-determinant term for a single permutation `σ`, over the whole index set. -/
def mooreTerm (A : Matrix n n M) (σ : Equiv.Perm n) : M :=
  mooreTermAux A σ Finset.univ

theorem orbitProd_one_eq_zero_of_moved (σ : Equiv.Perm n) (m : n) (h : (orbitFinset σ m).Nonempty)
    (hcard : 2 ≤ (orbitFinset σ m).card) :
    orbitProd (1 : Matrix n n M) σ (orbitFinset σ m) h = 0 := by
  have hne := orbitFinset_max_moved_of_card_ge_two σ m h hcard
  apply List.prod_eq_zero
  refine List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), ?_⟩
  show (1 : Matrix n n M) ((σ ^ (0 : ℕ)) ((orbitFinset σ m).max' h))
      ((σ ^ ((0 : ℕ) + 1)) ((orbitFinset σ m).max' h)) = 0
  rw [pow_zero, zero_add, pow_one, Equiv.Perm.one_apply]
  exact Matrix.one_apply_ne hne.symm

theorem orbitProd_one_eq_one_of_fixed (σ : Equiv.Perm n) (m : n) (h : (orbitFinset σ m).Nonempty)
    (hfix : σ m = m) :
    orbitProd (1 : Matrix n n M) σ (orbitFinset σ m) h = 1 := by
  have hcard : (orbitFinset σ m).card = 1 := by
    have hTeq : orbitFinset σ m = {m} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨mem_orbitFinset_self σ m, fun j hj => ?_⟩
      simp only [orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact (hj.eq_of_left hfix).symm
    rw [hTeq]
    exact Finset.card_singleton m
  unfold orbitProd
  rw [hcard, orbitFinset_max_eq_of_fixed σ m h hfix]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Matrix.one_apply]
  norm_num [hfix]

theorem mooreTermAux_one (σ : Equiv.Perm n) :
    ∀ S : Finset n, IsOrbitClosed σ S →
      mooreTermAux (1 : Matrix n n M) σ S = if ∀ i ∈ S, σ i = i then 1 else 0 := by
  refine mooreTermAux.induct (n := n) σ
    (motive := fun S => IsOrbitClosed σ S →
      mooreTermAux (1 : Matrix n n M) σ S = if ∀ i ∈ S, σ i = i then 1 else 0) ?_ ?_
  · intro S _hlet h ih hclosed
    have hstep : mooreTermAux (1 : Matrix n n M) σ S =
        orbitProd (1 : Matrix n n M) σ (orbitFinset σ (S.max' h)) (orbitFinset_nonempty σ _) *
          mooreTermAux (1 : Matrix n n M) σ (S \ orbitFinset σ (S.max' h)) := by
      rw [mooreTermAux, dif_pos h]
    rw [hstep]
    set T := orbitFinset σ (S.max' h) with hTdef
    set m := S.max' h with hmdef
    have hTsub : T ⊆ S := hclosed m (S.max'_mem h)
    have hTnonempty := orbitFinset_nonempty σ m
    have hTmax : T.max' hTnonempty = m := le_antisymm
      (Finset.le_max' S _ (hTsub (T.max'_mem hTnonempty)))
      (Finset.le_max' T m (mem_orbitFinset_self σ m))
    have hTcardpos : 0 < T.card := Finset.card_pos.mpr hTnonempty
    rcases Nat.lt_or_ge T.card 2 with hlt | hge
    · have hcard1 : T.card = 1 := by omega
      have hTeq : T = {m} := by
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
        have hmT : m ∈ T := mem_orbitFinset_self σ m
        rw [ha] at hmT
        simp at hmT
        rw [ha, hmT]
      have hfix : σ m = m := by
        have hmem : σ m ∈ T := by
          simp only [hTdef, orbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨1, by simp⟩
        rw [hTeq] at hmem
        simpa using hmem
      rw [orbitProd_one_eq_one_of_fixed σ m hTnonempty hfix, one_mul,
        ih (isOrbitClosed_sdiff σ hclosed h)]
      have hiff : (∀ i ∈ S, σ i = i) ↔ (∀ i ∈ S \ T, σ i = i) := by
        constructor
        · intro hall i hi
          exact hall i (Finset.mem_sdiff.mp hi).1
        · intro hrest i hi
          by_cases hiT : i ∈ T
          · rw [hTeq] at hiT
            simp at hiT
            rw [hiT]
            exact hfix
          · exact hrest i (Finset.mem_sdiff.mpr ⟨hi, hiT⟩)
      simp only [hiff]
      rfl
    · rw [orbitProd_one_eq_zero_of_moved σ m hTnonempty hge, zero_mul]
      rw [if_neg]
      intro hall
      have hmoved := orbitFinset_max_moved_of_card_ge_two σ m hTnonempty hge
      rw [hTmax] at hmoved
      exact hmoved (hall m (S.max'_mem h))
  · intro S _hlet h _
    rw [mooreTermAux, dif_neg h]
    have h' : ¬S.Nonempty := h
    rw [Finset.not_nonempty_iff_eq_empty.mp h']
    simp

/-- The Moore-determinant term of the identity matrix is `1` for `σ = 1`, and `0` otherwise:
exactly the expected identity-matrix behaviour of a genuine determinant. -/
theorem mooreTerm_one (σ : Equiv.Perm n) :
    mooreTerm (1 : Matrix n n M) σ = if σ = 1 then 1 else 0 := by
  unfold mooreTerm
  rw [mooreTermAux_one σ Finset.univ (isOrbitClosed_univ σ)]
  have hiff : (∀ i ∈ (Finset.univ : Finset n), σ i = i) ↔ σ = 1 := by
    constructor
    · intro hall
      ext i
      exact hall i (Finset.mem_univ i)
    · intro heq i _
      rw [heq]
      rfl
  simp only [hiff]

/-- The Moore determinant: the alternating sum, over all permutations `σ`, of `mooreTerm A σ`. -/
noncomputable def mooreDetSum (A : Matrix n n M) : M :=
  ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℤ) • mooreTerm A σ

/-- The Moore determinant of the identity matrix is `1`: only `σ = 1` contributes (every other
term has `mooreTerm 1 σ = 0` by `mooreTerm_one`), and `sign 1 = 1`. -/
theorem mooreDetSum_one : mooreDetSum (1 : Matrix n n M) = 1 := by
  unfold mooreDetSum
  have key : ∀ σ : Equiv.Perm n,
      (Equiv.Perm.sign σ : ℤ) • mooreTerm (1 : Matrix n n M) σ = if σ = 1 then (1 : M) else 0 := by
    intro σ
    rw [mooreTerm_one]
    split_ifs with hσ
    · simp [hσ]
    · simp
  simp_rw [key]
  simp

end MooreTerm

/-! ### `R`-linearity of the scaling degree

Now `M` is an `R`-algebra, so scaling by `r : R` is central in `M` and can be pulled through the
Moore-determinant product. -/

section Smul

variable {R : Type*} [CommRing R]
variable {M : Type*} [Ring M] [Algebra R M]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

private theorem list_prod_map_smul {ι : Type*} (l : List ι) (f : ι → M) (r : R) :
    (l.map (fun i => r • f i)).prod = r ^ l.length • (l.map f).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [ih, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ, mul_comm r]

omit [Fintype n] [DecidableEq n] in
theorem orbitProd_smul (r : R) (A : Matrix n n M) (σ : Equiv.Perm n) (S : Finset n)
    (h : S.Nonempty) :
    orbitProd (r • A) σ S h = r ^ S.card • orbitProd A σ S h := by
  unfold orbitProd
  have heq : (List.range S.card).map
      (fun i => (r • A) ((σ ^ i) (S.max' h)) ((σ ^ (i + 1)) (S.max' h))) =
      (List.range S.card).map
      (fun i => r • A ((σ ^ i) (S.max' h)) ((σ ^ (i + 1)) (S.max' h))) := by
    apply List.map_congr_left
    intro i _
    simp
  rw [heq, list_prod_map_smul, List.length_range]

theorem mooreTermAux_smul (r : R) (A : Matrix n n M) (σ : Equiv.Perm n) :
    ∀ S : Finset n, IsOrbitClosed σ S →
      mooreTermAux (r • A) σ S = r ^ S.card • mooreTermAux A σ S := by
  refine mooreTermAux.induct (n := n) σ
    (motive := fun S => IsOrbitClosed σ S →
      mooreTermAux (r • A) σ S = r ^ S.card • mooreTermAux A σ S) ?_ ?_
  · intro S _hlet h ih hclosed
    have hstep : mooreTermAux (r • A) σ S =
        orbitProd (r • A) σ (orbitFinset σ (S.max' h)) (orbitFinset_nonempty σ _) *
          mooreTermAux (r • A) σ (S \ orbitFinset σ (S.max' h)) := by
      rw [mooreTermAux, dif_pos h]
    have hstep' : mooreTermAux A σ S =
        orbitProd A σ (orbitFinset σ (S.max' h)) (orbitFinset_nonempty σ _) *
          mooreTermAux A σ (S \ orbitFinset σ (S.max' h)) := by
      rw [mooreTermAux, dif_pos h]
    rw [hstep, hstep']
    rw [ih (isOrbitClosed_sdiff σ hclosed h)]
    rw [orbitProd_smul]
    have hsub : orbitFinset σ (S.max' h) ⊆ S := hclosed (S.max' h) (S.max'_mem h)
    have hcard : (orbitFinset σ (S.max' h)).card + (S \ orbitFinset σ (S.max' h)).card = S.card := by
      rw [Nat.add_comm]
      exact Finset.card_sdiff_add_card_eq_card hsub
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, hcard]
  · intro S _hlet h _
    have hstep : mooreTermAux (r • A) σ S = 1 := by rw [mooreTermAux, dif_neg h]
    have hstep' : mooreTermAux A σ S = 1 := by rw [mooreTermAux, dif_neg h]
    have h' : ¬S.Nonempty := h
    rw [hstep, hstep', Finset.not_nonempty_iff_eq_empty.mp h', Finset.card_empty, pow_zero,
      one_smul]

/-- Scaling every entry of `A` by `r` scales `mooreTerm A σ` by `r ^ Fintype.card n`, for *any*
permutation `σ` -- the degree-`Fintype.card n` homogeneity expected of a genuine determinant. -/
theorem mooreTerm_smul (r : R) (A : Matrix n n M) (σ : Equiv.Perm n) :
    mooreTerm (r • A) σ = r ^ Fintype.card n • mooreTerm A σ := by
  unfold mooreTerm
  rw [mooreTermAux_smul r A σ Finset.univ (isOrbitClosed_univ σ), Finset.card_univ]

/-- Scaling every entry of `A` by `r` scales `mooreDetSum A` by `r ^ Fintype.card n`: the
degree-`Fintype.card n` homogeneity expected of a genuine determinant. -/
theorem mooreDetSum_smul (r : R) (A : Matrix n n M) :
    mooreDetSum (r • A) = r ^ Fintype.card n • mooreDetSum A := by
  unfold mooreDetSum
  simp_rw [mooreTerm_smul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_comm]

end Smul
