# Jordan

A Lean 4 / Mathlib formalization of Jordan algebras: the commutative, generally non-associative
algebras satisfying the Jordan identity `x² * (x * y) = x * (x² * y)`, together with the classical
examples (real, complex, quaternionic, and octonionic Hermitian matrices, and spin factors),
formal reality, Jordan triple systems, and the structure algebra of derivations.

Built against [Mathlib4](https://github.com/leanprover-community/mathlib4).

## Contents

| File | Description |
| --- | --- |
| [`Jordan/JordanAlgebra.lean`](Jordan/JordanAlgebra.lean) | The `JordanAlgebra` class itself, basic consequences of the Jordan identity, commuting left/right multiplications, and Jordan powers. |
| [`Jordan/JordanTriple.lean`](Jordan/JordanTriple.lean) | Linear Jordan triple systems (`{x, y, z}`), and the triple product induced by a Jordan algebra. |
| [`Jordan/StructureAlgebra.lean`](Jordan/StructureAlgebra.lean) | `JordanDerivation`: `R`-linear maps satisfying the Leibniz rule for the Jordan product, their module structure, and the commutator Lie algebra structure on derivations (`⁅D₁, D₂⁆`). Also `StructureAlgebra R M := M × JordanDerivation R M` (`L_a + D` acting on `M`), its own Lie algebra structure (via `toEnd` into `Module.End R M`, requiring `Invertible (2 : R)`), and `derivationSubalgebra`, the distinguished Lie subalgebra of derivations `(0, D)`. |
| [`Jordan/FormallyReal.lean`](Jordan/FormallyReal.lean) | Formal reality (`IsFormallyReal`): a sum of squares vanishes only trivially. `IsFormallyRealDetTrace`: a generic trace/determinant of rank `n`, its `states` (the cone of squares cut out by `trace x = 1`) and `pureStates` (idempotent states), convexity of the state space, and `expect`, the expectation value `trace (s * a)` of an observable `a` in a state `s`. Separately, consequences for the scalar ring `R`: a nontrivial formally real `M` forces `R` to be Artin-Schreier semireal (`-1` is never a sum of squares) and forces both `M` and `R` to have characteristic zero. |
| [`Jordan/RealQM.lean`](Jordan/RealQM.lean) | Symmetric matrices over a base ring `R`, as a Jordan algebra; formal reality; the `n = 1` case; a generic trace/determinant instance (`detTrace`, rank `Fintype.card n`) via the ordinary matrix trace and determinant. |
| [`Jordan/ComplexQM.lean`](Jordan/ComplexQM.lean) | "Complex" Hermitian matrices over `R` (via Mathlib's `QuadraticAlgebra`), generalizing the classical complex Hermitian case; formal reality and a generic trace/determinant instance (`detTrace`) built from the ordinary matrix trace/determinant. |
| [`Jordan/MooreDeterminant.lean`](Jordan/MooreDeterminant.lean) | The Moore determinant of a matrix over a non-commutative ring (`orbitProd`, `mooreTerm`, `mooreDetSum`): the classical replacement for `Matrix.det` when entries don't commute, with its `R`-linear scaling degree (`mooreDetSum_smul`) and identity-matrix value (`mooreDetSum_one`). Used by `QuaternionicQM` for the quaternionic determinant. |
| [`Jordan/QuaternionicQM.lean`](Jordan/QuaternionicQM.lean) | Quaternionic Hermitian matrices over `R` (via Mathlib's `QuaternionAlgebra`), plus the automorphism action of unit quaternions by conjugation; formal reality and a generic trace/determinant instance (`detTrace`) built from the ordinary trace and `MooreDeterminant.mooreDetSum`. |
| [`Jordan/Alternative.lean`](Jordan/Alternative.lean) | `IsAlternative`: the two weaker laws (`x * (x * y) = (x * x) * y`, `(y * x) * x = y * (x * x)`) that survive Cayley-Dickson doubling of an associative algebra, generic consequences (the associator's additivity and alternating sign under `S₃`), and the flexible law. |
| [`Jordan/Octonion.lean`](Jordan/Octonion.lean) | Generalized octonion algebras `Octonion R a b c` via Cayley-Dickson doubling, `IsAlternative`, the octonion norm (`mul_star_self_eq_scalarEmbed`) and its positive-definiteness, the self-adjoint (`1 x 1`) case, the `innerProduct` bilinear form with its multiplicative "adjoint" identities (`innerProduct_mul_left/right` and friends), and `nuclearInvolution`: for `a`, `b`, `c` non-zero-divisors, `Octonion R a b c` is a nuclear involution (`nuclear_rpart` proves Nuc ⊆ Center via coordinate tests against the Cayley-Dickson basis), taking that regularity as an explicit hypothesis rather than as a global instance. |
| [`Jordan/OctonionMatrix.lean`](Jordan/OctonionMatrix.lean) | Hermitian octonionic matrices `HermitianOctonionMatrix`; the `1 x 1` case, and the `2 x 2` case (the spin-factor identification via a trace/trace-free split, `ofSymmetricMatricesTwo`, complete). |
| [`Jordan/MatrixAssociator.lean`](Jordan/MatrixAssociator.lean) | `matrix_associator_apply` (McCrimmon's 1.2.0): the associator of `n x n` matrices over any `D`, reduced entrywise to a sum of associators/commutators of the entries. |
| [`Jordan/NuclearInvolution.lean`](Jordan/NuclearInvolution.lean) | `IsNuclear` (an element that associates trivially in every slot) and the `IsNuclearInvolution` class (star-fixed elements are nuclear; the nucleus is closed under commutators), plus the Nuclear Slipping Formula (`nuclear_comm_associator`: a nuclear element commutes with any associator value). |
| [`Jordan/HermitianMatrixAssociator.lean`](Jordan/HermitianMatrixAssociator.lean) | McCrimmon's Matrix Associator Facts (1.2.1)-(1.2.4): the diagonal/off-diagonal entries of `A * (B * C) - (A * B) * C` for `3 x 3` Hermitian matrices over an alternative `D` with nuclear involution. |
| [`Jordan/HermitianMatrixJordanIdentity.lean`](Jordan/HermitianMatrixJordanIdentity.lean) | `hermitian_jordan_identity`: the full, generic Jordan identity for `H_3(D,-)`, for any `D` with `[IsAlternative D] [StarRing D] [IsNuclearInvolution D]` — no Octonion-specific content. |
| [`Jordan/AlbertAlgebra.lean`](Jordan/AlbertAlgebra.lean) | The exceptional Jordan algebra `AlbertAlgebra` (`3 x 3` Hermitian octonionic matrices), for `a`, `b`, `c` non-zero-divisors. `ofAlbert`, the `JordanAlgebra` witness, applies `hermitian_jordan_identity` and bridges McCrimmon's undivided brace-associator form to `AlbertAlgebra`'s bullet product `⅟2 • (xy + yx)` -- fully axiom-free. Formal reality (`isFormallyReal`) and the generic trace/determinant (`detTrace`, the Freudenthal cubic-form `det`) build on `ofAlbert` and are likewise complete. All three take the non-zero-divisor hypotheses as explicit arguments rather than as global instances. |
| [`Jordan/SpinFactor.lean`](Jordan/SpinFactor.lean) | The spin factor Jordan algebra `V × R` from a symmetric bilinear form `B` on `V`, its determinant, formal reality under positive definiteness, and a generic trace/determinant instance (`detTrace`, rank `2`). |
| [`Jordan/CommNonAssocNF.lean`](Jordan/CommNonAssocNF.lean) | Design notes (no code yet) for a `simp`-proc that normalizes commutative, non-associative products, to replace manual `mul_comm`/`abel_nf` bookkeeping in the proofs above. |
| [`Jordan/Basic.lean`](Jordan/Basic.lean) | Placeholder. |

The [`find_cancel.py`](find_cancel.py) and [`gen_rules.py`](gen_rules.py) scripts are standalone
helpers used to search for cancellation identities among generated `mul_mul_eq`-style rewrite
rules, in support of the `CommNonAssocNF` tactic design.

See [`JORDAN_IDENTITY_PLAN.md`](JORDAN_IDENTITY_PLAN.md) for the detailed derivation history behind
`AlbertAlgebra`'s Jordan identity.

## Building

Requires [`elan`](https://github.com/leanprover/elan)/Lean 4 (toolchain version pinned in
[`lean-toolchain`](lean-toolchain)) and [Lake](https://github.com/leanprover/lake).

```sh
lake exe cache get   # download prebuilt Mathlib oleans
lake build
```
