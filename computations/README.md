# Computations for "Symmetries of Jordan Algebra Diagrams over Varying Base Rings"

This directory of [Cobord/JordanAlgebra](https://github.com/Cobord/JordanAlgebra) contains the Python and GAP code for the computations in Section 5 (spin factors) and Section 8.3
(integral points of the Baez–Schwahn chain) of the paper. Appendix A of the paper describes the same
files. Statement numbers below refer to the current version of the paper.

## Requirements

- Python 3 with `numpy` and `sympy` (the permutation-group library)
- GAP 4.12 or later, for `ident.g` only

All arithmetic that the paper relies on is exact (`fractions.Fraction`, or integers after scaling by 8).
Floating point is used only as a filter in the search, and every candidate is then verified exactly.

## Quick checks (seconds each)

```sh
python3 spin.py                 # Example 5.14 and a check of Lemma 5.10 for H_2(O)
python3 moufang.py              # Lemma 8.33 (Moufang lifts of the diagonal)
python3 binary_tetrahedral.py   # Example 8.37 (the subgroup D_8 x 2T)
```

`spin.py` needs only `octo.py` and the standard library. The other two also use `albert.py` and `numpy`.

## Integral chain pipeline (Section 8.3)

Run in this order, from this directory. Generated files (`*.pkl`, `autO.g`, `gauss.g`, `eis.g`) are ignored by git.

```sh
python3 aut_cache.py            # the 12096 automorphisms of O_Z, stored in autO.pkl
python3 run2.py gauss           # Lambda = Z[i]
python3 run2.py eis             # Lambda = Z[omega]
python3 analyze.py gauss 4      # about four minutes per case
python3 analyze.py eis 6
python3 color_rep.py
python3 eis_struct.py
python3 kd.py
python3 export_gap.py           # writes the GAP input files
gap ident.g                     # identifications in GAP
python3 brute_gauss.py          # optional independent recount, about twenty minutes
```

## Files

| File | Purpose | Paper |
|---|---|---|
| `octo.py` | Exact octonion arithmetic, the Coxeter integral orders and their 240 units | §8.3 |
| `albert.py` | The Albert algebra H_3(O_Q), its trace form and invariant trilinear form | §8.3 |
| `chain.py` | The choice of C, a floating-point filter, exact verification of a candidate automorphism | Prop. 8.34 |
| `chain2.py` | Enumeration of Aut(O_Z) and the backtracking search for integral extensions | Lemma 8.29, Prop. 8.34 |
| `aut_cache.py` | Computes and stores the 12096 automorphisms of O_Z | Lemma 8.29 |
| `run2.py` | Computes K_Lambda and tests every automorphism of B_Lambda ⊃ X_Lambda for an integral extension, verifying each exactly | Props. 8.30, 8.34 |
| `analyze.py` | Closure, components and structure of G_Lambda and K_Lambda; monomial form of Δ(96) | Prop. 8.34, Remark 8.36 |
| `color_rep.py` | The color group on C^⊥ ≅ C^3: determinant and irreducibility | Prop. 8.34 |
| `export_gap.py` | Writes Aut(O_Z), K_Lambda and G_Lambda as GAP permutation groups | Lemmas 8.29, 8.32 |
| `ident.g` | GAP identifications of Aut(O_Z), Δ(96) and Σ(72×3) | Lemmas 8.29, 8.32 |
| `eis_struct.py` | The structure 3^{1+2}_+ ⋊ Q_8 of the Eisenstein color group | Lemma 8.32 |
| `kd.py` | Orders 21, 16, 8, 6 of stabilizers in Aut(O_Z) for discriminants −7, −8, −11, −12 (not identified with color groups) | Appendix A |
| `brute_gauss.py` | Independent brute-force recount in the Gaussian case (no coset assumption) | Prop. 8.34 |
| `moufang.py` | Exact check that the three Moufang maps are Jordan automorphisms, and of the cubic norm formula | Lemma 8.33 |
| `binary_tetrahedral.py` | Exact check that the 192 maps of D_8 × 2T are distinct Jordan automorphisms preserving the chain | Example 8.37 |
| `spin.py` | Unit vectors and orthogonal groups of sums of squares over Z[1/2], the line stabilizer, an element of infinite order for n = 5, and a check of Lemma 5.10 | Example 5.14, Lemma 5.10 |

## Expected results

- |Aut(O_Z)| = 12096, with orbits of sizes 126 and 56.
- |K_{Z[i]}| = 96 (SmallGroup(96,64) = Δ(96)) and |K_{Z[ω]}| = 216 (SmallGroup(216,88) = Σ(72×3)).
- |G_{Z[i]}| = 6144 and |G_{Z[ω]}| = 31104; the gauge parts have index 2.
- O_n(Z[1/2]) has order 2, 8, 48, 1152 for n = 1, 2, 3, 4; the line stabilizer in Example 5.14(d) has order 96.
