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
| [`generate_walled_brauer_idempotents.ipynb`](generate_walled_brauer_idempotents.ipynb) | SageMath | Sects. 4.7, 5.6 | Computes the primitive idempotents ε_T of the Gelfand–Tsetlin basis; regeneration writes to `generated/wba_idempotents_db/` |
| [`bratteli_diagram_walled_brauer.ipynb`](bratteli_diagram_walled_brauer.ipynb) | SageMath | Figs. 1–3 | Bratteli diagram of B_{p,q} with edge contents; edges removed by the truncation len λˡ + len λʳ ≤ d are red |
| [`compute_matrix_units_and_blocks.nb`](compute_matrix_units_and_blocks.nb) | Mathematica | App. D | Converts the Sage idempotents to Mathematica, builds aligned matrix units ε^λ_ij and irreducible blocks; compares fresh exports with `idempotents/` and `blocks/` |
| [`app1.nb`](app1.nb) | Mathematica | Sect. 7.1, Ex. 7.1, Figs. 4–5 | Deciding the principal eigenvalue of a qubit state from n copies |
| [`app2.nb`](app2.nb) | Mathematica | Sect. 7.2 | Quantum majority vote for 3 inputs; LP (158), optimum F = 8/9 |
| [`app3.nb`](app3.nb) | Mathematica | Sect. 7.3, Exs. 7.2–7.3, Figs. 6–7 | Asymmetric 1 → 3 cloning: SDP blocks (160)–(169) and feasible regions |
| [`app4.nb`](app4.nb) | Mathematica | Sect. 7.4, Table 2 | Optimal sequential superchannel transforming n calls of U into U^T or U^{-1} |
| [`app4_tools.wl`](app4_tools.wl) | Wolfram Language | Sect. 7.4 | Shared diagram operations and the `App4Solve` implementation used by the numerical notebook and exact certificate |
| [`guess_magic_4_1_2.nb`](guess_magic_4_1_2.nb) | Mathematica | Sect. 7.4 | Exact optimal comb for U ↦ U^T with n = 4, d = 2 (fidelity 1) |
| [`archive/`](archive/) | Mathematica | – | Earlier working versions of `app4.nb` and a Mathematica Bratteli-diagram notebook, kept for reference (see [`archive/README.md`](archive/README.md)) |

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

- **SageMath 10.9** is the tested runtime for `wba_tools.py` and both Sage notebooks.
  The core code was originally developed with SageMath 9.4.
  `bratteli_diagram_walled_brauer.ipynb` uses `sage.misc.latex_standalone.TikzPicture`, which is part of SageMath
  since version 9.6; on SageMath 9.4/9.5, install the `slabbe` package and use `from slabbe import TikzPicture` in the
  last cell.
  The red edges, the content labels and the layered layout need `dot2tex` and `graphviz`; the PDF output needs a
  LaTeX installation with `tikz`, `tkz-graph` and `tkz-berge`.
  The tested combination is `dot2tex==2.11.3` with `pyparsing==3.1.4`; dot2tex 2.11.3 fails to parse the
  graph labels with pyparsing 3.3.3. Install compatible packages in the Sage environment when rendering figures.
- **Wolfram Mathematica** ≥ 12.3 for the notebooks (`LinearOptimization`, `SemidefiniteOptimization`);
  version **15.0.1**, including the front end, is the tested runtime.
  `app3.nb` uses `ResourceFunction["MatrixPartialTrace"]`, which needs access to the Wolfram Function Repository.
- Memory: the default notebooks use small examples. The optional exact comb expansion can become very large
  at n = 4, d = 3 (10,609 terms of size 120 × 120) and is disabled by default. The numerical
  path and exact certificate are separate. Large parameter choices still require care with memory
  and can take several minutes or longer. The four-call qubit certificate can be evaluated without
  running the numerical optimizer.

## Usage

Open the Mathematica notebooks from the repository root: they locate their inputs with `NotebookDirectory[]`.
Run each from the top in a fresh kernel or its isolated notebook context.
For the Sage notebooks, select a SageMath kernel whose working directory is the repository root.
Sections explain parameters, paper references and expected results; compact saved outputs come from native execution.

| Notebook | Parameters | Remarks |
|---|---|---|
| `app1.nb` | `d = 2`, `k = 2`, `pMax = 8` copies | the optional `traceNew` check takes a few minutes for n = 7 |
| `app2.nb` | `d = 4` by default; integer `d ≥ 3`, with wall `(3,1)` | d = 2 is not supported: trace preservation is imposed by matching diagram coefficients, which needs ψ^d to be faithful (eq. (118)) |
| `app3.nb` | d = 2 or 3, with wall `(1,3)` | aligned irreducible blocks and dimension-dependent permutation symmetries are checked before the cloning SDP; pᵢ denotes a depolarizing parameter |
| `app4.nb` | `task = "transpose"` or `"inverse"`; `n` calls; dimension `d`; default n = d = 3 | expected default fidelity 0.626597; reports equality/PSD residuals and Table 2 agreement; `verifyExactAnsatz` is an optional independent coefficient check |
| `guess_magic_4_1_2.nb` | fixed n = 4, d = 2 transposition | initializes itself, checks all 672 exact constraints and PSD/normalization/fidelity; the residual set must be `{0}` |

To regenerate the Sage data, run `generate_walled_brauer_idempotents.ipynb` with `max_total = 6`.
The default `max_total = 4` writes 28 files; six sites writes all 87 files through that rank.
Outputs go to `generated/wba_idempotents_db/`, keeping the supplied database intact.
Equivalent rational-function coefficients can have different printed forms.
The seven-site file is separate; rank-seven generation can take hours.
The Bratteli notebook writes editable TeX and PDF figures to `generated/bratteli_figures/`.

`compute_matrix_units_and_blocks.nb` reads the supplied Sage data and regenerates its selected `cases`
into a fresh temporary `outputRoot`, printed in the notebook.
The default cases `(4,1,2)` and `(4,1,3)` produce eight files and compare them exactly with the supplied
`idempotents/` and `blocks/` files. Matrix units are recomputed rather than reused from an old export.
Choose the destination explicitly when replacing data; the application notebooks normally read the supplied folders.

## Results

| Paper | Value | Notebook |
|---|---|---|
| Ex. 7.1 | p³_{2,2}(c), eq. (152); minimum 0.566968 at c₂ ≈ 0.913831 | `app1.nb` |
| Sect. 7.2 | F = 8/9 for all d ≥ 2 | `app2.nb` implements d ≥ 3 |
| Exs. 7.2, 7.3 | blocks (160)–(169); symmetric depolarizing parameter pᵢ = 5/9 (d = 2), 1/2 (d = 3) | `app3.nb` |
| Table 2 | U^T, d = 2: 0.5, 0.75, 0.933013, 1; d = 3: 0.222222, 0.407407, 0.626597, 0.799250 | `app4.nb` |
| Table 2 | U^{-1}, d = 2: as U^T; d = 3: 0.222222, 0.333333, 0.444444, 0.555556 | `app4.nb` |

For cloning, eq. (159) defines Φᵢ(ρ) = pᵢρ + (1 − pᵢ)I/d. The pure-state clone fidelity is
Fᵢ = pᵢ + (1 − pᵢ)/d, so the symmetric fidelities are **7/9** for d = 2 and **2/3** for d = 3.

## Paper conventions and corrections

- **Eq. (171), published p. 50:** the comb normalization should be Tr C = dⁿ⁺¹, with C₀ = 1.
  The printed Tr C = 1 is inconsistent with the objective and the values of Table 2.
- **Table 7, published p. 67:** `3,62,879` is a digit-grouping typo for **362,879**.
- **Eq. (85), published p. 28:** the clauses overlap when p = 0, k = 1. The code uses
  J₁ = δI for p = 0, consistent with the right-addition content in Sect. 5.3; for p > 0, J₁ = 0.
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
