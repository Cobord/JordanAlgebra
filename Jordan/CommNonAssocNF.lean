/-!
# TODO: a normal-form tactic for commutative, non-associative multiplication

Mathlib has no tactic for a magma where `*` is commutative but *not* associative (e.g.
`NonUnitalNonAssocCommRing`, which is exactly the shape of a `JordanAlgebra`'s underlying
multiplication): `ring`/`ring_nf` need associativity to flatten products into sorted monomials;
`noncomm_ring` is the opposite combination (associative, not-necessarily-commutative); `abel`/
`abel_nf` normalize only the additive structure and never look at `*` at all.

The proofs in `Jordan/JordanAlgebra.lean`, `Jordan/StructureAlgebra.lean`, and
`Jordan/JordanTriple.lean` all currently thread `mul_comm`/`jordan_mul_comm` through by hand
(explicit `rw`/`simp` calls) to align terms before `abel`/`abel_nf` can finish the job. A tactic
that mechanizes this would remove a lot of that manual bookkeeping.

## Planned approach

A `simp`-proc (not a full custom `Expr`-walking tactic) that, for any `a * b` in a type with a
commutative multiplication (targeting the generic `mul_comm` from `NonUnitalNonAssocCommRing`/
`CommMagma`, not anything Jordan-specific), rewrites `a * b ↦ b * a` iff `b` precedes `a` under
some fixed total order on terms (e.g. `Expr.lt`). This orients every rewrite in one direction, so
it terminates: after rewriting to `b * a`, re-checking the same condition on the new term compares
`a` after `b`, which no longer satisfies "precedes," so it won't fire again. Composed with
`abel`/`abel_nf` afterward, this should close most of the goals that currently need manual
`jordan_mul_comm` rewriting.

Open questions to resolve when implementing:
* Exact registration mechanism (`simproc`/`dsimproc`) and how to scope it to types with the right
  commutativity instance rather than firing on every `*` in scope.
* Whether `Expr.lt` alone gives a good/stable enough order, or something coarser (e.g. comparing
  leaf `FVarId`s only, ignoring subterm structure) converges faster on the deeply nested products
  that show up in `JordanTriple.lean`'s `triple_identity`.
* How it should interact with scalar multiplication (`•`) mixed into the same expressions.

`teorth/equational_theories` (Terence Tao's "Equational Theories Project", classifying implications
between magma equational laws) has related free-magma/term-rewriting infrastructure
(`FreeMagma.lean`, `Confluence*.lean`, `ConfluenceSystem.lean`) that may be worth checking for
reusable pieces -- in particular anything for normalizing a single non-associative product
("summand") under commutativity, which is exactly the sub-problem this tactic needs to solve
before `abel`/`abel_nf` can handle the surrounding sum.
-/
