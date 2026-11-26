# JordanDiagram

Formalization of *Symmetries of Jordan Algebra Diagrams over Varying Base Rings* (an earlier
draft is in [`Beyond/`](../Beyond/)), built on the `Jordan` library. Scalar extension is done for
a base map `R → S` (`F ↦ S ⊗[R] F`), and the diagram automorphism groups form a functor
`G_F : CommAlgCat R ⥤ GrpCat` (`autFunctor`). General families `{F_S}` with coherent base-change
maps `β_φ` are the structure `DiagramFamily`, and every family is the scalar extension
`F_S ≅ S ⊗[R] F_R` of its fiber over the base.

## Design choices

* **Morphisms of `Jord_R`** are Mathlib's non-unital algebra homomorphisms `A →ₙₐ[R] B`
  (`R`-linear and product-preserving, with no unit condition). This allows corner inclusions
  as arrows.
* **Isomorphisms and automorphisms.** `A ≃ⱼ[R] B` (`JordanEquiv`) is a linear bijection preserving
  the product. Mathlib has no group structure on `A →ₙₐ[R] A`, so `Aut_{Jord_R}(A)` is
  `jordanAut R A`, the subgroup of `A ≃ₗ[R] A` of multiplicative maps; `JordanEquiv.autEquiv`
  identifies the two.
* **Diagrams** are recorded concretely (`JordanDiagram R I`: algebras `obj i`, maps `map α`,
  functoriality) and are not bundled as functors into a Mathlib category; they form a category of
  their own, with natural transformations as morphisms. The chosen terminal object is the class
  `TerminallyPointed I`, with an instance for preorders with a top element.
* **Monomorphisms.** Terminal determination can be stated for monic terminal maps. Monomorphisms
  of `Jord_R` are injective, so here injectivity of each `νᵢ` is the hypothesis.
* **Shape-twisted automorphisms** over a functor `u` are isomorphisms `F ≅ u* F`
  (`TwistedIso F u`), which describe the morphisms over `(u, id_R)`. The shape-twisted group
  `G̃_F(R)` is `ShapeTwistedAut F`: a strict automorphism of the shape fixing `+` with compatible
  Jordan isomorphisms of the nodes, transported along `F(eqToHom _)` where objects are only
  propositionally equal. For a preorder shape the simpler `TwistedAut F` (with order
  automorphisms) is used in the wreath-product example.
* **Spin factors.** `SpinFactor.jordanAlgebra` is a definition that depends on `B.IsSymm`, so
  [`Algebra/SpinFactor.lean`](Algebra/SpinFactor.lean) adds a scoped instance under `[Fact B.IsSymm]`.
  A spin-factor diagram is indexed by any preorder with a top element, and its terminal node is
  `J(W ⊤, B|)`. For example `I = WithTop P` with `W ⊤ = V`.

## Files

The library has three parts:

* [`Algebra/`](Algebra/) concerns the symmetries of a single Jordan algebra, either generic or
  one of the algebras already formalized in `Jordan/`. Nothing in it mentions diagrams.
* [`MathlibMissing/`](MathlibMissing/) holds general constructions that Mathlib lacks and that
  the rest uses, candidates for upstreaming.
* [`Diagram/`](Diagram/) is the new content: terminally pointed diagrams, their automorphism
  groups and compatible derivations, and statements about them.

### `Algebra/`: symmetries of one algebra

| File | Contents |
| --- | --- |
| [`Automorphism.lean`](Algebra/Automorphism.lean) | `jordanAut R A`, setwise stabilizers `jordanAut.stab`, and lifting along an injective homomorphism: an automorphism or derivation of `J` that preserves `range ν` transports to `A` (`liftAut`, `liftDer`). |
| [`Equiv.lean`](Algebra/Equiv.lean) | `JordanEquiv` (`A ≃ⱼ[R] B`) with `refl`, `symm`, `trans`. `JordanEquiv.lift`: an isomorphism `J ≃ⱼ J'` carrying `range ν` onto `range ν'` lifts along injective `ν`, `ν'`. |
| [`Generation.lean`](Algebra/Generation.lean) | `jordanAut.ext_of_adjoin_eq_top`: an automorphism is determined by its values on a generating set (the single-algebra input to the finite detector criterion). |
| [`BaseChange.lean`](Algebra/BaseChange.lean) | With `2` invertible in `R`, `S ⊗[R] A` is a Jordan `S`-algebra (`instJordanAlgebra`). The proof goes through the fully linearized identity `lin`, which is multilinear, and `jordanExpr_add`. Also scalar extension of morphisms (`baseChangeHom`, injective for flat `S`), of automorphisms (`baseChangeAut`) and of derivations (`baseChangeDer`). Descent (`descendAut`): an automorphism of `E ⊗ A` preserving `1 ⊗ A` is `id ⊗ h` for an automorphism `h` of `A`, when `a ↦ 1 ⊗ a` is injective. |
| [`Functor.lean`](Algebra/Functor.lean) | Transport along any `φ : S →ₐ[R] T`: `mapLin φ f` is the unique `T`-linear map with `mapLin φ f ∘ (φ ⊗ 1) = (φ ⊗ 1) ∘ f`, and `mapAut φ : Aut(S ⊗ A) →* Aut(T ⊗ A)`. Functor laws `mapAut_id_alg`, `mapAut_comp_alg`, and `mapAut_baseChangeAut` (compatibility with extension from `R`). The same for derivations: `mapDer`, which is additive and bracket-preserving. |
| [`Orthogonal.lean`](Algebra/Orthogonal.lean) | If `B` is symmetric and nonsingular on `W`, then `V = W ⊕ W⊥` (`isCompl_orthogonal`), and `stabEquivProd : Stab_{O(V,B)}(W) ≃* O(W, B) × O(W⊥, B)`. |
| [`OrthogonalFlag.lean`](Algebra/OrthogonalFlag.lean) | For an internal direct sum `V = ⨁ Uᵢ` of mutually orthogonal pieces: `stabPiecesEquivPi : Stab_{O(V,B)}(Uᵢ ∀ i) ≃* ∏ᵢ O(Uᵢ, B)`. With `B` nondegenerate on each piece and a linear order on the indices, `stabFlagEquivPi` gives the same for the flag `W_j = ⨆_{i ≤ j} Uᵢ`. |
| [`OrthogonalFlagIso.lean`](Algebra/OrthogonalFlagIso.lean) | `nonempty_flagIsometry_iff`: two orthogonal flags with nondegenerate pieces are isometric exactly when their pieces are pairwise isometric. `skewFlagEquivPi`: the skew endomorphisms preserving the flag are `⊕ᵢ o(Uᵢ, B)`, by restriction (the Lie algebra analogue). |
| [`Tower.lean`](Algebra/Tower.lean) | For `R → S → T`: the coherence `cancelJordanEquiv : T ⊗[S] (S ⊗[R] A) ≃ⱼ[T] T ⊗[R] A`, the extension `autTower : Aut(S ⊗ A) →* Aut(T ⊗ A)`, and `autTower_baseChangeAut`: extending from `R` to `S` and then to `T` is extending from `R` to `T`. |
| [`SpinFactor.lean`](Algebra/SpinFactor.lean) | For `V`, `V'` free, `2` invertible and any symmetric forms, including degenerate ones: `isometryEquiv : Isometry B B' ≃ (J(V, B) ≃ⱼ J(V', B'))` (`g ↦ g ⊕ id`), `autEquivOrthogonal : O(V, B)(R) ≃* Aut J(V, B)`, and `derEquivSkew : o(V, B)(R) ≃ Der J(V, B)` (`X ↦ X ⊕ 0`). |
| [`SpinFactorFormallyReal.lean`](Algebra/SpinFactorFormallyReal.lean) | `SpinFactor.isFormallyReal_iff_posDef`: over a real closed field, `J(V, B)` is formally real exactly when `B` is positive definite (the converse of `SpinFactor.isFormallyRealPos`). |
| [`OctonionNorm.lean`](Algebra/OctonionNorm.lean) | The norm of the Cayley–Dickson algebra with generators squaring to `a, b, c` (`Octonion R a b (-c)`) is diagonal with coefficients `1, -a, -b, ab, -c, ac, bc, -abc` (`Octonion.mul_star_self_eq_diag`), all positive over an ordered ring when `a, b, c < 0` (`Octonion.normCoeff_pos`). Its polar form is diagonal with the same coefficients (`Octonion.innerProduct_eq_sum`), so it is **nonsingular exactly when `a`, `b`, `c` are units** (`Octonion.bijective_innerProduct_iff`). |
| [`HermitianTwo.lean`](Algebra/HermitianTwo.lean) | **Two-by-two Hermitian matrices are spin factors** over every Cayley–Dickson stage: `ofSymmetricMatricesTwo : H₂(C₃) → J(C₃ ⊕ R)`, `!![ρ+α, x; x̄, ρ-α] ↦ ((x, α), ρ)`, for the form `n(x, y) + αβ`, is `R`-linear (`hermitianTwoLinearEquiv`); the stages `cdStage k` (`C₀ = R ⊆ C₁ ⊆ C₂ ⊆ C₃`) are closed under product and conjugation, and the map restricts to `H₂(Cₖ) ≅ J(Cₖ ⊕ R)` (`forall_mem_cdStage_iff`), where `n` involves only the first `2ᵏ` norm coefficients. |
| [`FiniteSubgroupStabilizer.lean`](Algebra/FiniteSubgroupStabilizer.lean) | For a faithful action `ρ : G →* GL(M)` on a finitely generated `Z[1/2]`-module: every finite subgroup preserves a finitely generated additive subgroup `L` with `Z[1/2] L = M` (`IsFGSpanning`, `exists_isFGSpanning_le_stabilizer`). When `M` is free of rank `n`, such an `L` is free of rank `n` over `ℤ` (`IsFGSpanning.finrank_eq`), so by Minkowski every finite subgroup has order at most `3^(n²)` (`card_le`) and lies in a maximal finite subgroup (`exists_maximal_finite`); if the stabilizers of all such `L` are finite, the maximal finite subgroups are the maximal members among them (`maximal_finite_iff`). |
| [`GaloisTwist.lean`](Algebra/GaloisTwist.lean) | For `L/k` and `θ : L ⊗ A ≅ L ⊗ B`, the automorphisms `twistAut θ σ = θ (σ ⊗ 1) θ⁻¹ (σ⁻¹ ⊗ 1)` form a cocycle (`twistAut_mul`), changed by coboundaries under change of `θ` (`twistAut_baseChange_trans`, `twistAut_trans_ofAut`); Galois-equivariant isomorphisms descend (`exists_baseChangeEquiv_eq`). |
| [`TwistedDescent.lean`](Algebra/TwistedDescent.lean) | **Twisted Galois descent**: for a cocycle `a`, the fixed points of `a(σ) ∘ (σ ⊗ 1)` form a Jordan algebra `twistForm a` over `k` (`JordanAlgebra.ofSubmodule`) with `L ⊗ twistForm a ≅ L ⊗ B` (`twistIso`) whose cocycle is `a` (`twistAut_twistIso`). |
| [`DyadicFinite.lean`](Algebra/DyadicFinite.lean) | **Finiteness at `2`.** `Z[1/2]` is discrete in `ℝ × ℚ₂` (`exists_int_of_norm_le_one`), so a rational form positive on nonzero vectors and anisotropic over `ℚ₂` has finitely many vectors of `Z[1/2]^ι` of a given value (`finite_setOf_zHalf`), and a group acting faithfully on a finite free `Z[1/2]`-module preserving such a form is finite (`finite_of_form`); e.g. `O(V, B)(Z[1/2])` (`finite_orthogonalGroup`). |
| [`StabilizerFinite.lean`](Algebra/StabilizerFinite.lean) | Under a `G`-invariant biadditive `ℚ`-valued form with `β(x, x) > 0` for `x ≠ 0`, the stabilizer of every finitely generated spanning subgroup is finite (`finite_stabilizer_of_form`), so `maximal_finite_iff` holds unconditionally (`maximal_finite_iff_of_form`). |
| [`SquareZero.lean`](Algebra/SquareZero.lean) | For `e² = 0` and a Jordan derivation `D`, `1 + e D` is a Jordan automorphism (`sqZeroAut`), with `(1 + e D)(1 + e D') = 1 + e (D + D')` and, for `e² = e'² = 0`, commutator `1 + e e' [D, D']` (`sqZeroAut_commutator`). |
| [`DualNumber.lean`](Algebra/DualNumber.lean) | Over the dual numbers `S[ε]`: the `ε`-component `sndTensor`, the decomposition of `S[ε] ⊗ A`, and the derivation `derOfDual g` with `g = 1 + ε D` for an automorphism `g` reducing to the identity modulo `ε` (`sqZeroAut_derOfDual`, `derOfDual_sqZeroAut`). |
| [`Dyadic.lean`](Algebra/Dyadic.lean) | `ZHalf`, the ring `Z[1/2]`. A unital map `Z[1/2] → R` is unique (`zHalf_ringHom_subsingleton`) and exists exactly when `2` is a unit in `R` (`nonempty_zHalf_ringHom_iff`); ring homomorphisms between `Z[1/2]`-algebras commute with the structure maps (`comp_algebraMap_zHalf`, `zHalfAlgHomEquiv`), so `CAlg_{Z[1/2]}` is the full subcategory of commutative rings with `2` invertible. |

### `MathlibMissing/`: general constructions not in Mathlib

| File | Contents |
| --- | --- |
| [`LieRingCat.lean`](MathlibMissing/LieRingCat.lean) | `LieRingHom L L'` (`L →⁅⁆ L'`): additive maps with bracket preservation as a field, with `id`, `comp`, `ext`, `map_lie`. `LieRingCat`, the category of Lie rings, with the same API as `GrpCat`. |
| [`PiLie.lean`](MathlibMissing/PiLie.lean) | The componentwise Lie ring and Lie algebra structures on a Pi type. |
| [`SemilinearBaseChange.lean`](MathlibMissing/SemilinearBaseChange.lean) | `IsSemilinearBaseChange f`: a `σ`-semilinear `f : M → N` is a base change along `σ : S → T` (universal property of `M → T ⊗_S M`, without making `T` an `S`-algebra). `lift`, `ext`, `extend`/`extendEquiv` of endomorphisms, and `extend_mul`, `extend_leibniz` for Jordan algebras. |
| [`PowerSeriesOrder.lean`](MathlibMissing/PowerSeriesOrder.lean) | `PowerSeries.lowestCoeff` (multiplicative over a domain) and `PowerSeriesLC A`, the lowest-coefficient order on `A⟦X⟧` as a `LinearOrder` and `IsStrictOrderedRing`, built from the cone of series with nonnegative lowest coefficient. |
| [`PowerSeriesMatrix.lean`](MathlibMissing/PowerSeriesMatrix.lean) | `Matrix.eq_one_of_pow_eq_one`: over a torsion-free `R`, a matrix over `R⟦X⟧` with constant term `1` and finite order is `1` (the kernel of `GL_n(R⟦X⟧) → GL_n(R)` is torsion-free). |
| [`FractionRingOrder.lean`](MathlibMissing/FractionRingOrder.lean) | The ordered fraction field of a totally ordered ring: `FractionRing R` ordered by the cone `{a / b | ab ≥ 0}` (`posCone`) as an `IsStrictOrderedRing`, extending the order of `R` (`algebraMap_le_iff`), and the unique such order (`le_iff_of_order`). |
| [`GaloisDescent.lean`](MathlibMissing/GaloisDescent.lean) | Galois descent for vector spaces over a finite Galois `L/k`: invariants of `L ⊗ M` are `1 ⊗ M` (`exists_tmul_of_forall_rTensor_eq`), and **Speiser's lemma** `L ⊗ V^ρ ≅ V` for a semilinear action (`bijective_liftBaseChange_fixedPoints`, via Dedekind's independence of characters). |
| [`AnisotropicBound.lean`](MathlibMissing/AnisotropicBound.lean) | Over a normed field with compact closed balls (`ℝ`, `ℚ_[p]`), an anisotropic quadratic form satisfies `c ‖v‖² ≤ ‖vᵀ A v‖` with `c > 0` (`Matrix.exists_pos_mul_norm_sq_le_norm`). |
| [`PosDefIntegerPoints.lean`](MathlibMissing/PosDefIntegerPoints.lean) | A rational quadratic form positive on nonzero integer vectors takes values `≤ C` at only finitely many integer vectors (`Matrix.finite_setOf_int_le`), via positivity over `ℝ` (`Matrix.pos_of_pos_int`) and compactness of the sphere. |
| [`GrothendieckCocartesian.lean`](MathlibMissing/GrothendieckCocartesian.lean) | In the covariant Grothendieck construction `∫ F` of a pseudofunctor, the lifts `(f, 𝟙)` are strongly cocartesian (`isStronglyCocartesian_cocartesianLift`), so `forget F` is an opfibration (`exists_isStronglyCocartesian`). |
| [`Minkowski.lean`](MathlibMissing/Minkowski.lean) | Minkowski's lemma: for `m ≥ 3`, the kernel of `GL_N(ℤ) → GL_N(ℤ/m)` is torsion-free (`Matrix.eq_one_of_pow_eq_one_of_modEq`, via the prime-power case `Matrix.eq_one_of_pow_eq_one_of_modEq_prime_pow`), so every finite subgroup of `GL_N(ℤ)` embeds in `GL_N(ℤ/m)` (`Matrix.injOn_reduce`). |

### `Diagram/`: the diagram layer

| File | Contents |
| --- | --- |
| [`Basic.lean`](Diagram/Basic.lean) | `TerminallyPointed`, `JordanDiagram`, restriction along a functor, the terminal algebra `J`, the terminal maps `ν i` and the terminal relation `ν_map`, and the images `Aᵢ`. |
| [`Group.lean`](Diagram/Group.lean) | The diagram automorphism group `autGroup`, terminal evaluation `ev`, and terminal determination: `ev_injective`, `range_ev`, and `autGroupEquivStab : G_F(R) ≃* ⋂ᵢ Stab(Aᵢ)`. Also `restrictHom`. |
| [`Derivation.lean`](Diagram/Derivation.lean) | The compatible derivations `derAlgebra` as a Lie subalgebra, the Lie homomorphism `evDer`, `evDer_injective`, `range_evDer` (image `{D : D(Aᵢ) ⊆ Aᵢ}`), and `restrictDer`. |
| [`DualNumber.lean`](Diagram/DualNumber.lean) | **The Lie algebra of `G_F`.** `1 + e D` as a diagram automorphism for `e² = 0` (`sqZeroAutGroup`), with commutator `1 + e e' [D, D']` (`sqZeroAutGroup_commutator`); `D ↦ 1 + ε D` is an isomorphism of abelian groups from `g_F(S)` onto the kernel of `G_F(S[ε]) → G_F(S)` (`dualAutEquiv`). |
| [`Wedge.lean`](Diagram/Wedge.lean) | `IsWedge P₁ P₂` and `autGroupEquivWedge : G_F(R) ≃* G_{F₁}(R) ×_{Aut(J)} G_{F₂}(R)`. For derivations, `wedgeDer_injective` and `range_wedgeDer`. |
| [`Iso.lean`](Diagram/Iso.lean) | `DiagramIso F F'` (isomorphisms in a fiber) and its terminal determination `terminalEquiv` (isomorphisms `↔` `h : J ≃ⱼ J'` with `h(Aᵢ) = A'ᵢ`). `TwistedIso F u = DiagramIso F (u* F)`. `twistedIdEquiv` identifies the twisted isomorphisms over `𝟭` with `G_F(R)`, the kernel of `G̃_F(R) → Aut(I⁺, +)`. `twistedTerminalEquiv` is terminal determination for twisted automorphisms. |
| [`Family.lean`](Diagram/Family.lean) | **Families over varying base rings**: `DiagramFamily R I`, a diagram `F_S` over every commutative `R`-algebra `S` with coherent base-change maps `β_φ` (semilinear, multiplicative, natural, base changes, `β_id = id`, `β_{χφ} = β_χ β_φ`). `G_F` and `g_F` as functors `CAlg_R ⥤ Grp`, `CAlg_R ⥤ LieRing` (`autFunctor`, `derFunctor`), with `G_F(φ)(g) ∘ β_φ = β_φ ∘ g`. `baseChangeFamily F` (`S ↦ S ⊗ F`) recovers `autMap`, `derMap`. Conversely `DiagramFamily.baseIso`: every family is the scalar extension of its fiber over the base, `F_S ≅ S ⊗[R] F_R` via `β_{ι_S}`. |
| [`Ordered.lean`](Diagram/Ordered.lean) | **The ordered scalar category** `OrdScalar k`: totally ordered rings with an order-preserving `k`-algebra structure, morphisms the continuous order-preserving `k`-algebra maps. `OrdScalar.forget` to `CommAlgCat k`, and the ordered symmetry functors (`G_F`, `g_F` restricted along it), for diagrams and for families. `OrdScalar.exists_pos_lt_of_injective`: injective morphisms are coinitial on positives. |
| [`OrderedPowerSeries.lean`](Diagram/OrderedPowerSeries.lean) | `A⟦t⟧` with the lowest-coefficient order is an ordered scalar object, with `t` a positive infinitesimal. The constant-term map is a morphism (`constTermHom`), the constant-series inclusion is not continuous (`not_continuous_algebraMap`), and there is no morphism `A ⟶ A⟦t⟧` (`isEmpty_hom`): the base is not initial. |
| [`Product.lean`](Diagram/Product.lean) | `prodAutEquiv : Aut((S × S') ⊗ A) ≃* Aut(S ⊗ A) × Aut(S' ⊗ A)` and **`autGroupProdEquiv : G_F(S × S') ≃* G_F(S) × G_F(S')`**, the map being `(G_F(fst), G_F(snd))` (`autMap_prod_bijective`). |
| [`PowerSeries.lean`](Diagram/PowerSeries.lean) | The constant-term map `constCoeffAlg : S⟦X⟧ → S`, split by `constAlg`. For finite free nodes and torsion-free `S`: the kernel of `G_F(S⟦X⟧) → G_F(S)` is torsion-free (`autMap_const_eq_one`), finite subgroups embed (`injOn_autMap_const`), and the map is split (`autMap_const_comp_autMap_C`). |
| [`Twisted.lean`](Diagram/Twisted.lean) | For a shape that is a preorder: `TwistedAut F` (an order automorphism `σ` of the shape with Jordan isomorphisms `F(i) ≃ F(σ i)` compatible with the arrows) and its group structure, **the shape-twisted group `G̃_F(R)`**. `shapeHom : G̃_F(R) →* Aut(I)` and `ofAut : G_F(R) →* G̃_F(R)`, with `ofAut_injective` and `range_ofAut`: `1 → G_F(R) → G̃_F(R) → Aut(I)` is exact. `toTwistedIso`/`ofTwistedIso` relate it to `TwistedIso`. |
| [`TwistedGeneral.lean`](Diagram/TwistedGeneral.lean) | For an arbitrary terminally pointed shape: `ShapeAut I`, the group `Aut(I⁺, +)` of strict automorphisms fixing `+`, and `ShapeTwistedAut F`, **the shape-twisted group** of pairs `(u, θ)`. `range_ofAut`: `1 → G_F(R) → G̃_F(R) → Aut(I⁺, +)` is exact. `terminalEquiv`: with injective terminal maps, `(u, θ) ↦ (u, θ₊)` identifies `G̃_F(R)` with the pairs `(u, h)` with `h(Aᵢ) = A_{u(i)}` (`terminalPairs`). |
| [`NodePreimage.lean`](Diagram/NodePreimage.lean) | **An additive subgroup at the terminal node**: for `L ⊆ J` and `Lᵢ = νᵢ⁻¹(L)` (`nodePreimage`), `g₊(L) = L` iff `gᵢ(Lᵢ) = Lᵢ` for all `i` (`image_top_eq_iff`); the `Lᵢ` span when `L` does (`exists_pow_smul_mem_nodePreimage`) and are finitely generated when `L` is (`finite_nodePreimage`). |
| [`MaximalFinite.lean`](Diagram/MaximalFinite.lean) | Over `Z[1/2]`, `G_F` acts faithfully on `∏ᵢ F(i)` (`nodesRep`) and, for injective terminal maps, on `F(+)` (`terminalRep`), so the results of `Algebra/FiniteSubgroupStabilizer.lean` apply: `finite_subgroups_nodes`, `finite_subgroups_terminal`. |
| [`Pseudofunctor.lean`](Diagram/Pseudofunctor.lean) | Diagrams `I → Jord_R` form a category (`JordanDiagram.category`, natural transformations). Restriction along shapes is strictly functorial (`restrictFunctor_id`, `restrictFunctor_comp`), giving `restrictionFunctor R : Cat₊ᵒᵖ ⥤ Cat` whose Grothendieck construction is a fibration (`isFibered_restriction`). Scalar extension `baseChangeFunctor` commutes strictly with restriction and is coherent (`baseChangeComp`, `baseChangeId`, `compHom_assoc`, …): `baseChangePseudofunctor`, whose Grothendieck construction is an opfibration over `CAlg_{Z[1/2]}` (`exists_isStronglyCocartesian_baseChange`), and **`diagramPseudofunctor : Cat₊ᵒᵖ × CAlg_{Z[1/2]} → Cat`**, `(I, R) ↦ Fun(I, Jord_R)`. |
| [`Representability.lean`](Diagram/Representability.lean) | **The diagram group functor is representable**, for finite free nodes: over the polynomial ring `P` in the entries of matrices `Xᵢ`, `Yᵢ` at each node, the relations are the coordinates of the generic defects (`XᵢYᵢ - 1`, `YᵢXᵢ - 1`, multiplicativity and naturality on basis vectors), and `B = P ⧸ (relations)` satisfies `(B →ₐ[k] S) ≃ G_F(S)` naturally in `S` (`algHomEquiv`, `algHomEquiv_comp`), is of finite type for finitely many objects (`finiteType`), and is a quotient of the algebra `k[∏ GL]` representing `∏ᵢ GL(F(i))`, compatibly with `G_F ⊆ ∏ᵢ GL(F(i))` (`glEquiv`, `toRep`, `glEquiv_comp_toRep`). Packaged without bases as `JordanDiagram.representable`. |
| [`GroupScheme.lean`](Diagram/GroupScheme.lean) | **The diagram group scheme.** `T ↦ G_F(Γ(T))` on schemes over `Spec k` (`pointsFunctor`, through `globalSections`) is represented by `Spec B` (`representableBy`, via `specRingHomEquiv` from the vendored Stacks files), so `Spec B` is a group object over `Spec k` (`grpObj`) with `pointsIso : yonedaGrpObj (Spec B) ≅ pointsFunctor F` as presheaves of groups; likewise `∏ᵢ GL(F(i))` (`glPoints`, `grpObjGL`, `pointsIsoGL`). `Spec B ⟶ Spec k[∏ GL]` is a homomorphism (`isMonHom_of_comp_mul`: multiplicativity on points suffices) and a closed immersion, taking a diagram automorphism to its components: `closedSubgroup : ClosedSubgroupScheme` (vendored). Basis-free: `groupScheme`. |
| [`Wreath.lean`](Diagram/Wreath.lean) | `spinTwist`: a shape automorphism `σ` and an isometry with `g(Wᵢ) = W_{σ i}` give a twisted automorphism `g ⊕ id` of a spin-factor diagram. `Disc κ` (discrete order), with `permShape_surjective`: every automorphism of `WithTop (Disc κ)` is a permutation. `wreathDiagram BU κ` (copies of `U` below `κ → U`) and **`wreathEquiv : G̃_F(R) ≃* O(U)^κ ⋊ Perm κ`**, with the shape map the permutation part. |
| [`Finiteness.lean`](Diagram/Finiteness.lean) | The finite detector criterion: a faithful action on a finite `X` gives `\|G\| ≤ \|X\|!`. `card_autGroup_le`: a finite, stable, Jordan-generating `X ⊆ J` bounds `\|G_F(R)\|` by `\|X\|!`. |
| [`Forms.lean`](Diagram/Forms.lean) | **Forms and Galois cohomology.** For a finite Galois `L/k`: forms of `F` split by `L` (`Form`), Galois cocycles in `G_F(L)` (`GaloisCocycle`) and `H1`. The cocycle of a form (`Form.cocycle`) is well defined on isomorphism classes, isomorphic exactly for cohomologous cocycles (`Form.cohomologous_cocycle_iff`), and every cocycle comes from a form (`GaloisCocycle.form_cocycle`): **`formsEquivH1 : FormClass L F ≃ H1 L F`**. |
| [`SpinFactor.lean`](Diagram/SpinFactor.lean) | `spinDiagram B W` for monotone `W : I →o Submodule R V`. Its terminal maps are injective, with image `R 1 ⊕ Wᵢ`. `spinDiagramAutEquiv : G_F(R) ≃* Stab_{O(W ⊤, B)}(W)`, `spinDiagramDerEquiv : g_F(R) ≃ Stab_{o(W ⊤, B)}(W)`, and `spinDiagramIsoEquiv`: isomorphisms of spin-factor diagrams are isometries of the configurations. |
| [`SpinFactorFinite.lean`](Diagram/SpinFactorFinite.lean) | **Dyadic points of definite spin-factor diagrams**: over `Z[1/2]`, with `B` positive and the top piece anisotropic over `ℚ₂`, `G_F(Z[1/2])` is finite (`finite_spinDiagram`); for an orthogonal flag it suffices that every piece is anisotropic over `ℚ₂` (`finite_stabFlag`). |
| [`Functor.lean`](Diagram/Functor.lean) | **The functor `G_F`**: `autFunctor F : CommAlgCat R ⥤ GrpCat`, `S ↦ Aut(S ⊗[R] F)`, built from `autMap F φ : G_F(S) →* G_F(T)` with `autMap_id`, `autMap_comp`, and `autMap_comp_autBaseChange`. For `R = Z[1/2]`, `CommAlgCat R` is `CAlg_{Z[1/2]}`. **The functor `g_F`**: `derFunctor F : CommAlgCat R ⥤ LieRingCat`, built from the Lie ring homomorphisms `derMap F φ : g_F(S) →⁅⁆ g_F(T)` with `derMap_id`, `derMap_comp`, and `derMap_derBaseChange`. |
| [`BaseChange.lean`](Diagram/BaseChange.lean) | `F.baseChange S = S ⊗[R] F`. `autBaseChange : G_F(R) →* G_F(S)`, injective when every `F(i) → S ⊗ F(i)` is (`autBaseChange_injective`), so every finite subgroup embeds with an image of the same order (`subgroupEquivMap`, `card_map_autBaseChange`). Its image is the set of automorphisms preserving every `1 ⊗ F(i)` (`range_autBaseChange`), with `autGroupEquivPreserving`. `autTowerDiagram : G_F(S) →* G_F(T)` for `R → S → T`, and `autTowerDiagram_comp_autBaseChange`: it composes with `G_F(R) → G_F(S)` to give `G_F(R) → G_F(T)`. `derBaseChange` on compatible derivations, additive and bracket-preserving. Terminal maps stay injective along flat `R → S`. |

Build with `lake build JordanDiagram`. The default target is still the `jordan` executable. There
are no `sorry`s. The headline results use only `propext`, `Classical.choice` and `Quot.sound`.

## Next steps

1. **Compactness.** No topology is put on `G_F(ℝ)` or `G_F(ℚ₂)`. The finiteness half of
   "finite exactly when compact at `2`" is proved for groups preserving a form anisotropic over
   `ℚ₂` (`ZHalf.finite_of_form`); the general statement in terms of compactness, compactness of
   orthogonal groups of anisotropic forms and noncompactness for isotropic ones, and the
   infiniteness half (via the Borel–Harish-Chandra theorem) are not done. For definite spin-factor
   diagrams and orthogonal flags only the "anisotropic at `2` ⇒ finite" direction is proved.
2. **Invariant positive forms.** Finiteness of stabilizers is proved under an invariant positive
   `ℚ`-valued form (`finite_stabilizer_of_form`). The trace form `tr(L_{x∘y})` (its invariance, its
   positivity for formally real algebras, and the resulting compactness of the real points) is not
   done.
3. **Forms.** The classification by `H¹(Gal(L/k), G_F(L))` is proved for a finite Galois `L/k`
   (`formsEquivH1`). Not done: forms over a ring (étale descent, `H¹_ét`) and over a separable
   closure; the specialization to spin-factor diagrams (forms are again spin-factor diagrams, `H¹`
   of a flag is the product over the pieces); the classification of the pieces by quadratic-form
   invariants (Hasse–Minkowski over `ℚ`).
4. **The two-by-two Cayley–Dickson chain.** Its pieces are formalized (`HermitianTwo.lean`,
   orthogonal flags), but not the assembled chain diagram with its group
   `O⟨1,1⟩ × μ₂ × O(N_{C₁}) × O(N_{C₂})` and isomorphism criterion.
5. **Exceptional diagrams.** Beyond formal reality and nonsingularity of the octonion norm, nothing
   about diagrams in the exceptional algebra is formalized: the type of its automorphism group
   scheme, the frame diagrams, the Baez–Schwahn chain and its integral points.
6. **Arbitrary octonion parameters.** The Jordan identity for `H₃` of the Cayley–Dickson algebra is
   proved for parameters that are not zero divisors, not for all parameters.
