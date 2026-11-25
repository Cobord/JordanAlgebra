# Vendored files from the Stacks Project in Lean

The Lean files under this directory are copied, **unmodified**, from
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) (*The Stacks Project in Lean*, Axiom), at
commit
[`f56a316ddf7a930906d88b78d6f9a2668cffd0cf`](https://github.com/AxiomMath/Stacks/tree/f56a316ddf7a930906d88b78d6f9a2668cffd0cf).
That project is licensed under the Apache License, Version 2.0; a copy of the license is in
[`LICENSE`](LICENSE). The upstream repository has no `NOTICE` file.

The files keep their upstream paths and module names, so they can be replaced by a dependency on
the full library without changing any import, and they keep their `@[stacks …]`, `@[ega …]` and
`@[sga …]` attribution attributes, which link each declaration to the Stacks Project tag or
EGA/SGA item it formalizes. They are built as the separate library `StacksVendored` (see the
project's `lakefile.toml`).

| File | Upstream tier | Contents |
| --- | --- | --- |
| `StacksCore/Tactic/StacksAttribute.lean` | StacksCore (human-reviewed) | the `@[stacks_fixed]` attribute and `add_to_stacks` |
| `StacksCore/Tactic/EgaSgaAttribute.lean` | StacksCore (human-reviewed) | the `@[ega]`/`@[sga]` attributes |
| `StacksFrontier/AlgebraicGeometry/Scheme/SpecRingHomEquiv.lean` | StacksFrontier (AI-written, unreviewed upstream) | morphisms `X ⟶ Spec R` as ring maps `R →+* Γ(X)` |
| `StacksFrontier/AlgebraicGeometry/GroupScheme/Examples/GeneralLinear.lean` | StacksFrontier (AI-written, unreviewed upstream) | the general linear group scheme `GL_n` (Stacks Tag 022W): representability, group structure, base change |
| `StacksFrontier/AlgebraicGeometry/GroupScheme/Subgroups/Defs.lean` | StacksFrontier (AI-written, unreviewed upstream) | closed and open subgroup schemes and the factorization criterion (Stacks Tags 047D, 0G8L) |

These are exactly the files needed for `GL_n` and closed subgroup schemes: the closure of
`GeneralLinear` and `Subgroups/Defs` under imports from the Stacks library. To update, copy the
same paths from a newer upstream commit and record it above; any local change to a file must be
stated in that file, as the Apache License requires.
