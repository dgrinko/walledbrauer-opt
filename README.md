# walledbrauer-opt

Code and data for

> D. Grinko and M. Ozols, *Linear Programming with Unitary-Equivariant Constraints*,
> Commun. Math. Phys. **405**, 278 (2024), [doi:10.1007/s00220-024-05108-1](https://doi.org/10.1007/s00220-024-05108-1),
> [arXiv:2207.05713](https://arxiv.org/abs/2207.05713).

A semidefinite program for a matrix variable X on (C^d)^{⊗p} ⊗ (C^d)^{*⊗q} that commutes with
U^{⊗p} ⊗ Ū^{⊗q} for all U ∈ U(d) can be reduced, under an additional symmetry, to a linear program whose size does
not depend on d. The reduction expresses X in the primitive idempotents of the algebra A^d_{p,q} of partially
transposed permutations, which are computed inside the walled Brauer algebra B^d_{p,q} with Jucys–Murphy elements
(Sect. 5 of the paper). This repository contains the code that computes these idempotents (SageMath), the resulting
database, and the Mathematica notebooks for the four applications of Sect. 7.

## Contents

| File | Language | Paper | What it does |
|---|---|---|---|
| [`wba_tools.py`](wba_tools.py) | SageMath | Sects. 3.2, 4.7, 5 | Walled Brauer algebra B^δ_{p,q} (`WalledBrauerAlgebra`), Jucys–Murphy elements (eq. 85), Bratteli diagram, contents (Sect. 5.3), interpolating polynomials (eq. 77), the matrix representation ψ^d_{p,q} (eq. 41) |
| [`generate_walled_brauer_idempotents.ipynb`](generate_walled_brauer_idempotents.ipynb) | SageMath | Sects. 4.7, 5.6 | Computes the primitive idempotents ε_T of the Gelfand–Tsetlin basis and writes `wba_idempotents_db/` |
| [`bratteli_diagram_walled_brauer.ipynb`](bratteli_diagram_walled_brauer.ipynb) | SageMath | Figs. 1–3 | Bratteli diagram of B_{p,q} with edge contents; edges removed by the truncation len λˡ + len λʳ ≤ d are red |
| [`compute_matrix_units_and_blocks.nb`](compute_matrix_units_and_blocks.nb) | Mathematica | App. D | Converts the Sage idempotents to Mathematica, builds aligned matrix units ε^λ_ij and the irreducible blocks of every diagram; writes `idempotents/` and `blocks/` |
| [`app1.nb`](app1.nb) | Mathematica | Sect. 7.1, Ex. 7.1, Fig. 5 | Deciding the principal eigenvalue of a qubit state from n copies |
| [`app2.nb`](app2.nb) | Mathematica | Sect. 7.2 | Quantum majority vote for 3 inputs; LP (158), optimum F = 8/9 |
| [`app3.nb`](app3.nb) | Mathematica | Sect. 7.3, Exs. 7.2–7.3, Figs. 6–7 | Asymmetric 1 → 3 cloning: SDP blocks (160)–(169) and feasible regions |
| [`app4.nb`](app4.nb) | Mathematica | Sect. 7.4, Table 2 | Optimal sequential superchannel transforming n calls of U into U^T or U^{-1} |
| [`guess_magic_4_1_2.nb`](guess_magic_4_1_2.nb) | Mathematica | Sect. 7.4 | Exact optimal comb for U ↦ U^T with n = 4, d = 2 (fidelity 1) |
| [`archive/`](archive/) | Mathematica | – | Earlier working versions of `app4.nb` and a Mathematica Bratteli-diagram notebook, kept for reference (see [`archive/README.md`](archive/README.md)) |
| [`review/`](review/) | Python | all | Independent re-implementation used to verify the database and every number in Sect. 7 and Appendix E (see [`REVIEW.md`](REVIEW.md)) |

### Data

| Folder | Written by | Read by | Content |
|---|---|---|---|
| `wba_idempotents_db/` | `generate_walled_brauer_idempotents.ipynb` | `app2.nb`, `app3.nb`, `compute_matrix_units_and_blocks.nb` | `primitive_p_q.txt`: primitive idempotents of B^z_{p,q} for a symbolic δ = z (use for d ≥ p+q, substituting z → d); `primitive_p_q_d.txt`: idempotents for 2 ≤ d < p+q (their images under ψ^d_{p,q} are the idempotents of A^d_{p,q}). All p+q ≤ 6, plus (7,0,2). |
| `idempotents/` | `compute_matrix_units_and_blocks.nb` | `app4.nb`, `app1.nb` (optional) | `primitive_p_q_d.m`, `metadata_p_q_d.m` (irrep dimensions, Bratteli paths, diagram basis), `elementary_p_q_d.m` (matrix units ε^λ_ij) |
| `blocks/` | `compute_matrix_units_and_blocks.nb` | `app4.nb` | `blocks_p_q_d.m`: the irreducible blocks X_λ(σ) of every walled Brauer diagram σ |
| `app4_data/` | – | `guess_magic_4_1_2.nb` | `eq_4_1_2_exact.m`: the exact comb constraints for U^T, n = 4, d = 2 |

**File format of `wba_idempotents_db/`.** Each file is the `str()` of a Python dictionary
`{path: idempotent}`. A path is a tuple of bipartitions `([λˡ], [λʳ])` from the root `([], [])` to a leaf of the
Bratteli diagram; an idempotent is a linear combination of diagrams `B{{a, b}, ...}` whose coefficients are rational
functions of `z` (or rationals for numeric `d`). In a diagram, label `i > 0` is node `i` of the top row and `-i` is
node `i` of the bottom row; nodes `1..p` are left of the wall. The product `a*b` places `a` on top of `b` (eq. (30)),
and the top row of a diagram labels the row index of ψ^d_{p,q}(σ), i.e. the bra in eq. (44), so that ψ is a
homomorphism.

`wba_idempotents_db/primitive_8_0_2.txt` (210 MB) exceeds GitHub's file-size limit and is not included; regenerate it
with `generate_walled_brauer_idempotents.ipynb` if needed (nothing in the repository uses it).

## Pipeline

```
wba_tools.py ─▶ generate_walled_brauer_idempotents.ipynb ─▶ wba_idempotents_db/*.txt ─┬─▶ app2.nb, app3.nb
   (Sage)              (Sage)                                                      │
                                                                                    └─▶ compute_matrix_units_and_blocks.nb
                                                                                              │  (Mathematica)
                                                                                              ▼
                                                                         idempotents/*.m, blocks/*.m ─▶ app4.nb, app1.nb
```

`app1.nb` does not need any data: the traces it uses are pasted from Sage (`pData`). Its `traceNew` recomputes them from
`idempotents/` (data exist for n ≤ 7), and an optional cell checks that both agree.

## Requirements

- **SageMath** ≥ 9.4 for `wba_tools.py` and the two Sage notebooks (the code also runs on Sage 10.x).
  `bratteli_diagram_walled_brauer.ipynb` uses `sage.misc.latex_standalone.TikzPicture`, which was merged into
  SageMath from the `slabbe` package in 2021; on an older Sage, install `slabbe` and import `TikzPicture` from it.
  The red edges, the content labels and the layered layout need `dot2tex` and `graphviz`; the PDF output needs a
  LaTeX installation with `tikz`, `tkz-graph` and `tkz-berge`.
- **Wolfram Mathematica** ≥ 12.3 for the notebooks (`LinearOptimization`, `SemidefiniteOptimization`).
  `app3.nb` uses `ResourceFunction["MatrixPartialTrace"]`, which needs access to the Wolfram Function Repository.
- **Python 3** with `numpy`, `scipy`, `sympy` and `cvxpy` for the verification scripts in `review/`.
- Memory: `app4.nb` with n = 4, d = 3 (`{4, 1, 3}`) builds very large symbolic expressions (one failed run reported a
  13.6 GB intermediate expression), so it needs a large-memory machine. All other cases run on a laptop.

## Usage

Open the notebooks from the repository root: they locate the data folders with `NotebookDirectory[]`.

| Notebook | Parameters | Remarks |
|---|---|---|
| `app1.nb` | `d = 2`, `k = 2`, `pMax = 8` copies | the optional `traceNew` check takes a few minutes for n = 7 |
| `app2.nb` | `{p, q, d} = {3, 1, d}` with `d ≥ 3` | d = 2 is not supported: trace preservation is imposed by matching diagram coefficients, which needs ψ^d to be faithful (eq. (118)); the value F = 8/9 at d = 2 is confirmed in `review/` |
| `app3.nb` | `{p, q, d} = {1, 3, 2}` or `{1, 3, 3}` | a check cell after `In[1174]` tests that the blocks read off the eigenvectors are aligned (must return ≈ 0); `blocks/blocks_1_3_d.m` give the same blocks independently of any basis choice |
| `app4.nb` | `{p, q, d} = {n, 1, d}` for U^T, `{n + 1, 0, d}` for U^{-1}; default `{3, 1, 3}` (expected 0.626597) | the comb is normalised as Tr C = d^{n+1} (C₀ = 1), so that the objective is the average channel fidelity; eq. (171) of the paper says Tr C = 1, see [`REVIEW.md`](REVIEW.md) |
| `guess_magic_4_1_2.nb` | – | not self-contained: first evaluate the definition cells of `app4.nb` with `{p, q, d} = {4, 1, 2}`; its last cell checks the 672 exact constraints in `app4_data/eq_4_1_2_exact.m` and must return `{0}` |

To rebuild the data: run `generate_walled_brauer_idempotents.ipynb` from the repository root (writes
`wba_idempotents_db/`; p + q ≤ 6 takes a few minutes, p + q = 7 several hours), then
`compute_matrix_units_and_blocks.nb` with the (p, q, d) you need in its two `Do` loops (writes `idempotents/` and
`blocks/`; existing `elementary_*.m` files are reused, delete them to force a recomputation). With the current
`wba_tools.py` the regenerated idempotents are mathematically identical to the stored ones (72 of 87 files byte for
byte; the other 15 differ only in how coefficients are printed).

## Results

| Paper | Value | Notebook |
|---|---|---|
| Ex. 7.1 | p³_{2,2}(c), eq. (152); minimum 0.566968 at c₂ ≈ 0.913831 | `app1.nb` |
| Sect. 7.2 | F = 8/9 for all d ≥ 3 | `app2.nb` |
| Exs. 7.2, 7.3 | blocks (160)–(169); symmetric optimum 5/9 (d = 2), 1/2 (d = 3) | `app3.nb` |
| Table 2 | U^T, d = 2: 0.5, 0.75, 0.933013, 1; d = 3: 0.222222, 0.407407, 0.626597, 0.799250 | `app4.nb` |
| Table 2 | U^{-1}, d = 2: as U^T; d = 3: 0.222222, 0.333333, 0.444444, 0.555556 | `app4.nb` |

All of these were reproduced independently with the Python code in `review/`; see [`REVIEW.md`](REVIEW.md).

## Notes

- The notebooks were cleaned up in October 2026 by editing their source text (fixes listed in
  [`REVIEW.md`](REVIEW.md)), without Mathematica. Saved outputs that no longer matched the code were removed; re-run a
  notebook from the top before relying on its outputs. `app1.nb` and `app3.nb` still contain outputs from several
  sessions (non-sequential `In`/`Out` labels, mixed d = 2 and d = 3 state in `app3.nb`).
- Partial-trace constraints are imposed by comparing diagram coefficients, which requires ψ^d to be faithful on the
  traced-out algebra (eq. (118) of the paper); `app4.nb` instead maps these constraints to irreducible blocks and
  works for every d.

## Citation

```bibtex
@article{GrinkoOzols2024,
  author  = {Grinko, Dmitry and Ozols, Maris},
  title   = {Linear Programming with Unitary-Equivariant Constraints},
  journal = {Communications in Mathematical Physics},
  volume  = {405},
  number  = {12},
  pages   = {278},
  year    = {2024},
  doi     = {10.1007/s00220-024-05108-1},
  eprint  = {2207.05713},
  archivePrefix = {arXiv}
}
```
