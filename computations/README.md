# Computations for "Symmetries of Jordan Algebra Diagrams over Varying Base Rings"

This directory of [Cobord/JordanAlgebra](https://github.com/Cobord/JordanAlgebra) contains the Python and GAP code for the paper's computations about spin factors over Z[1/2]
and about the integral points of the Baez–Schwahn chain. The paper's appendix on computations describes the same
files. Results are named by content below rather than by number, since the paper's numbering changes.

## Requirements

- Python 3 with `numpy` and `sympy` (the permutation-group library)
- GAP 4.12 or later, for `ident.g` only

With [uv](https://docs.astral.sh/uv/), `uv sync` installs the pinned dependencies from `uv.lock`;
then use `uv run python <script>.py` in place of `python3 <script>.py` below.
`uv run python main.py` runs everything below in parallel (about a minute and a half once the
`.pkl` caches exist; `--fresh` rebuilds them, `--brute` adds the brute-force recount).

All arithmetic that the paper relies on is exact (`fractions.Fraction`, or integers after scaling by 8).
Floating point is used only as a filter in the search, and every candidate is then verified exactly.

## Quick checks (seconds each)

```sh
python3 spin.py                 # sums of squares over Z[1/2], and H_2(O) as a spin factor
python3 moufang.py              # Moufang lifts of the diagonal
python3 binary_tetrahedral.py   # the subgroup D_8 x 2T
```

`spin.py` needs only `octo.py` and the standard library. The other two also use `albert.py` and `numpy`.

## Integral chain pipeline

Run in this order, from this directory. Generated files (`*.pkl`, `autO.g`, `gauss.g`, `eis.g`) are ignored by git.

```sh
python3 aut_cache.py            # the 12096 automorphisms of O_Z, stored in autO.pkl
python3 run2.py gauss           # Lambda = Z[i]
python3 run2.py eis             # Lambda = Z[omega]
python3 analyze.py gauss 4      # about a minute per case
python3 analyze.py eis 6
python3 color_rep.py
python3 eis_struct.py
python3 kd.py
python3 export_gap.py           # writes the GAP input files
gap ident.g                     # identifications in GAP
python3 brute_gauss.py          # optional independent recount, about twenty minutes
```

## Files

| File | Purpose | Paper result |
|---|---|---|
| `octo.py` | Exact octonion arithmetic, the Coxeter integral orders and their 240 units | integral chain (setup) |
| `albert.py` | The Albert algebra H_3(O_Q), its trace form and invariant trilinear form | integral chain (setup) |
| `chain.py` | The choice of C, a floating-point filter, exact verification of a candidate automorphism | integral points of the chain |
| `chain2.py` | Enumeration of Aut(O_Z) and the backtracking search for integral extensions | automorphisms of the integral octonions; integral points of the chain |
| `aut_cache.py` | Computes and stores the 12096 automorphisms of O_Z | automorphisms of the integral octonions |
| `run2.py` | Computes K_Lambda and tests every automorphism of B_Lambda ⊃ X_Lambda for an integral extension, verifying each exactly | structure of the integral chain group; integral points of the chain |
| `analyze.py` | Closure and components of G_Lambda, normality of K_Lambda; monomial form of Δ(96) | integral points of the chain; the orders of the groups |
| `color_rep.py` | The color group on C^⊥ ≅ C^3: determinant and irreducibility | the color groups |
| `export_gap.py` | Writes Aut(O_Z), K_Lambda and G_Lambda as GAP permutation groups | automorphisms of the integral octonions; Δ(96) and Σ(72×3) |
| `ident.g` | GAP identifications of Aut(O_Z), Δ(96) and Σ(72×3) | automorphisms of the integral octonions; Δ(96) and Σ(72×3) |
| `eis_struct.py` | The structure 3^{1+2}_+ ⋊ Q_8 of the Eisenstein color group | Δ(96) and Σ(72×3) |
| `kd.py` | Orders 21, 16, 8, 6 of stabilizers in Aut(O_Z) for discriminants −7, −8, −11, −12 (not identified with color groups) | appendix on computations |
| `brute_gauss.py` | Independent brute-force recount in the Gaussian case (no coset assumption) | integral points of the chain |
| `moufang.py` | Exact check that the three Moufang maps are Jordan automorphisms, and of the cubic norm formula | Moufang lifts of the diagonal |
| `binary_tetrahedral.py` | Exact check that the 192 maps of D_8 × 2T are distinct Jordan automorphisms preserving the chain | finite subgroup from the quaternion stage |
| `spin.py` | Unit vectors and orthogonal groups of sums of squares over Z[1/2], the line stabilizer, an element of infinite order for n = 5, and a check that H_2(O) is a spin factor of a diagonal form | sums of squares; two-by-two Hermitian matrices |

## Expected results

- |Aut(O_Z)| = 12096, with orbits of sizes 126 and 56.
- |K_{Z[i]}| = 96 (SmallGroup(96,64) = Δ(96)) and |K_{Z[ω]}| = 216 (SmallGroup(216,88) = Σ(72×3)).
- |G_{Z[i]}| = 6144 and |G_{Z[ω]}| = 31104; the gauge parts have index 2.
- O_n(Z[1/2]) has order 2, 8, 48, 1152 for n = 1, 2, 3, 4; the stabilizer of the line through (1, 1, 1, 1) for n = 4 has order 96.
