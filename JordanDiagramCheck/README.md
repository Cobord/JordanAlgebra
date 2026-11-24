# JordanDiagramCheck

A [comparator](https://github.com/leanprover/comparator) check of the main results of
[`JordanDiagram`](../JordanDiagram/).

* [`Challenge.lean`](Challenge.lean): the **trusted** statements, each with `sorry`. This is the
  file to review. It says, in Lean, what the formalization claims about the paper.
* [`Solution.lean`](Solution.lean): the same statements, proved from the library.
* [`comparator.json`](comparator.json): the theorems to compare and the permitted axioms
  (`propext`, `Quot.sound`, `Classical.choice`).

A passing run means each Solution theorem has exactly the Challenge statement, uses only the
permitted axioms, and is accepted by the Lean kernel.

## Statements

| Challenge theorem | Paper |
| --- | --- |
| `terminal_determination` | Prop. 3.6 |
| `compatible_derivations` | Prop. 3.8 |
| `wedge` | Prop. 3.12 |
| `iso_terminal_determination` | Props. 3.14, 5.7 (terminal determination for isomorphisms) |
| `finite_detector` | Prop. 4.2 with Lemma 4.3 |
| `scalar_extension` | Lemma 2.4 (commutativity and the Jordan identity on `S ⊗[R] A`, for Mathlib's product) |
| `autMap_functor` | Prop. 3.3 (functor laws for `G_F`, compatibility with `G_F(R) → G_F(S)`) |
| `derMap_functor` | Prop. 3.8 (functor laws for `g_F`, brackets preserved) |
| `comparison_injective`, `comparison_image` | Prop. 7.9(b), 7.9(c) |
| `spinFactor_aut`, `spinFactor_der` | Lemma 5.5, stated elementarily: automorphisms are `(v, r) ↦ (g v, r)` with `g` an isometry, derivations are `(v, r) ↦ (X v, 0)` with `X` skew |
| `orthogonal_splitting` | Cor. 5.10, one nonsingular member |
| `spin_diagram_group` | Prop. 5.6 |

The statements use the library's definitions (`JordanDiagram`, `autGroup`, `ev`, `derAlgebra`,
`autMap`, …), which are part of the trusted import closure. `Challenge.lean` imports the whole
library, so the check pins the statements and the axioms, but does not separate the trusted
definitions from the untrusted proofs in the library.

## Running

```sh
JordanDiagramCheck/run.sh                      # comparator at ../comparator
COMPARATOR_DIR=/path/to/comparator JordanDiagramCheck/run.sh
```

Expected output ends with

```
Lean default kernel accepts the solution
Your solution is okay!
```

Setup: the comparator repository is archived, and its functionality moved into Lean core as
`lake comparator` from v4.35.0. This project is on v4.31.0, so use the standalone tool at its last
v4.31.0 commit:

```sh
git clone https://github.com/leanprover/comparator ../comparator
cd ../comparator && git checkout fd2e25d
lake build comparator
(cd .lake/packages/lean4export && lake build)
```

After a toolchain bump to v4.35.0 or later, switch to `lake comparator` with the same
`comparator.json`.

## Sandbox

Comparator runs every build and export step under `landrun`, which needs Landlock (Linux ≥ 5.13).
On a kernel without it, [`landrun-bwrap.sh`](landrun-bwrap.sh) takes landrun's place. It accepts
comparator's landrun command line and runs the step under bubblewrap with:

* the filesystem read-only, except `.lake` during the build;
* a private `/tmp` and `/run` (no sockets from `/run`);
* no network;
* an environment cleared except for the variables comparator passes.

`run.sh` additionally runs the whole check under `systemd-run -p RestrictAddressFamilies=~AF_UNIX`,
as comparator's README recommends, so Unix sockets elsewhere (e.g. under `$HOME`) cannot be
reached either.

Not reproduced: landrun's per-path *execute* restriction, since bubblewrap has no per-mount
`noexec`.

Checks done on this setup:
* writes outside `.lake` fail ("Read-only file system");
* TCP fails ("Network is unreachable");
* unlisted environment variables are dropped;
* `socket(AF_UNIX)` fails ("Address family not supported");
* replacing a Solution proof with `sorry` is rejected ("Illegal axiom detected: 'sorryAx'").
