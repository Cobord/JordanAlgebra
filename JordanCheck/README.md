# JordanCheck

A `lake comparator` check of the main results of the [`Jordan`](../Jordan/) library.

* [`Challenge.lean`](Challenge.lean): the **trusted** statements, each with `sorry`. This is the
  file to review.
* [`Solution.lean`](Solution.lean): the same statements, proved from the library.

Both are collected, together with [`JordanDiagramCheck`](../JordanDiagramCheck/), by the top-level
[`Challenge.lean`](../Challenge.lean) and [`Solution.lean`](../Solution.lean) named in
[`comparator.json`](../comparator.json). Run `lake comparator` (or `lake comparator --paranoid`)
in the project root.

## Statements

| Challenge theorem | Content |
| --- | --- |
| `linearized_jordan_identity` | With `2` invertible, `[L_a, L_{bc}] + [L_b, L_{ca}] + [L_c, L_{ab}] = 0` |
| `linearized_fundamental_formula` | With `2` invertible, `L_{(bd)c} = L_{bd}L_c + L_{cd}L_b + L_{bc}L_d - L_bL_cL_d - L_dL_cL_b` |
| `powers_operator_commute` | With `2` invertible, multiplications by any two powers of an element commute |
| `inner_derivation` | With `2` invertible, `[L_x, L_y]` is a derivation |
| `jordan_triple_identity` | With `2` invertible, the triple product `{x,y,z} = (xy*)z + (zy*)x - (xz)y*` of a Jordan algebra with involution (antilinear in `y`) satisfies the Jordan triple identity |
| `formallyReal_scalars` | A nontrivial formally real Jordan `R`-algebra forces `R` semireal and of characteristic zero |
| `spinFactor_jordan` | The spin factor of a symmetric form is commutative and satisfies the Jordan identity |
| `spinFactor_formallyReal` | The spin factor of a positive definite form is formally real |
| `symmetric_formallyReal` | Symmetric matrices over an ordered ring are formally real |
| `complexHermitian_formallyReal` | Hermitian matrices over a definite quadratic algebra are formally real |
| `quaternionicHermitian_formallyReal` | Hermitian matrices over a definite quaternion algebra are formally real |
| `hermitian_three_jordan_identity` | The Jordan identity for `3 × 3` Hermitian matrices over an alternative ring with nuclear involution |
| `octonion_alternative` | Generalized octonions satisfy both alternative laws |
| `albert_jordan` | The Albert algebra product is commutative and satisfies the Jordan identity (non-zero-divisor parameters) |
| `albert_formallyReal` | The Albert algebra over definite octonions is formally real |
