# Archive

Superseded and exploratory Mathematica notebooks, kept for reference. They are not needed to reproduce the
paper: Sect. 7.4 and Table 2 are covered by [`app4.nb`](../app4.nb) and
[`guess_magic_4_1_2.nb`](../guess_magic_4_1_2.nb), and Figs. 1–3 by
[`bratteli_diagram_walled_brauer.ipynb`](../bratteli_diagram_walled_brauer.ipynb), all in the repository root.
`app4_v5.nb`, `app4_v6.nb` and `app4_v7.nb` are successive Save-As copies of the notebook that became `app4.nb`
(= v8, April 2023).

## Before opening a notebook

- **Location.** The `app4_*` notebooks locate their data with `NotebookDirectory[]` (`idempotents/`, `blocks/`,
  `app4_data/`). Copy a notebook to the repository root before evaluating it. For `app4_v7.nb`, also copy
  `archive/app4_data/eq_4_1_2_50_left.m` to `app4_data/`. `app4_data/ansatz_4_1_2.m` is imported by v5 and v7
  but is not in the repository; it is written by their own Export cell.
- **Old file-naming rule.** These notebooks name data files with
  `FName[name,p,q,d] = NotebookDirectory[]<>name<>"_"<>ToString[p]<>"_"<>ToString[q]<>If[d>=p+q,"","_"<>ToString[d]]`.
  This rule drops the `_d` suffix when d ≥ p+q, giving names such as `idempotents/metadata_2_0.m`,
  `blocks/blocks_2_0.m` or `idempotents/elementary_1_1.m`. Those d-less files were not kept. They were not
  d-generic: `elementary_1_1.m` and `blocks_1_1.m` held d = 2 data. Two of them were also corrupt:
  `elementary_2_1.m` mixed d = 6 idempotents with matrix units normalised at d = 3, and `blocks_2_1.m` was not a
  representation for any d. The repository only has `_p_q_d` files. To run an archived notebook, replace
  `If[d>=p+q,"","_"<>ToString[d]]` in its first cell by `"_"<>ToString[d]`, the rule `app4.nb` uses. Without that
  change, every case that needs a d-less name stops at a failed `Import`. That includes {p,q,d} = {4,1,2}, which
  needs `metadata_2_0` and `blocks_2_0`.
- **Two register conventions.** v5 and `app4.nb` put P last (O_1..O_n, P | I_1..I_n, F) and use the (p,q) matrix
  units on both registers ("P-last"). v6 and v7 put P first (P, O_1..O_n) and expand the left register in the
  matrix units of A_{q,p}, `elementary_q_p_d.m` ("P-first"). The variables `x[λ,μ,i,j,k,l]` (written `xλμ…`)
  therefore mean different things in the two conventions, and constraint files and solutions cannot be mixed
  between them.
- **Saved outputs** come from several kernel sessions, often for parameter sets other than the visible one. The
  notebooks cannot be re-run top to bottom as saved.

## Notebooks

**`app4_v5.nb`** (edited until Sept. 2022). U^T with {p,q,d} = {4,1,2}, i.e. n = 4 calls and d = 2, in the
P-last formulation of `app4.nb` at machine precision. It contains the exact-certificate check for (4,1,2). With the
hand-made solution `guessAnsatz` (the one in `guess_magic_4_1_2.nb`):
- `eqConstrExact /. guessAnsatz // Simplify` is all zeros (Out[759]; the constraints come from
  `app4_data/eq_4_1_2_exact.m`);
- the objective is exactly 1 (Out[737]);
- `Solve` fixes the five irrational entries a1..a5 (Out[733]).

The numerical SDP gives 0.9999999989 (Out[484]). Caveats:
- The ansatz cell (In[760]) already substitutes `guessAnsatz`, which is defined much further down.
- In[737] overwrites `objective` with a hard-coded exact expression.
- The saved SDP had 228 variables, after an elimination step that is not in the notebook (the full problem has 932).
- The computed constraints are overwritten by an `Import` of `eq_4_1_2_exact.m`.
- Out[50]–Out[52], Out[77], Out[363] and Out[610]/Out[611] belong to other runs.

The maintained form of this certificate is [`guess_magic_4_1_2.nb`](../guess_magic_4_1_2.nb).

**`app4_v6.nb`** (edited until April 2023, last saved with Mathematica 14.0). A P-first rewrite of v5 at 50-digit
precision that covers U^T, with (p,q) = (n,1), and U^{-1}, with (p,q) = (n+1,0). The saved state mixes three
parameter sets:
- (3,1,2), U^T with n = 3, d = 2: a hand reduction to parameters a1..a15 and a feasible point `soltest`. Its
  objective, (2+√3)/4 = 0.933013, matches Table 2 but is never printed. The reduced SDP In[308] is infeasible by
  construction: it adds a4 == 1/3 and a13 == 0 to the relation a13 == 3 a4.
- (3,0,2): only a failed `Import` of `eq_3_0_2_exact.m`, a file that is not in the upload. Its `Import::nffil`
  message, which showed a local path, was deleted for the repository, so the notebook no longer shows this.
- The final {1,1,3}, U^T with n = 1, d = 3. **Its saved value 0.29055 (Out[301]) is an artefact; Table 2 gives
  0.222222 = 2/9.** The parameter cell was evaluated after the matrix units, ansatz and constraints of an earlier
  run, and the old naming rule loads the d = 2 file `elementary_1_1.m` for d = 3.

The notebook also carries v5 cells (P-last guess checks) copied together with their outputs. In[108] calls
functions with a stale argument count. For (4,1,2) in its own convention it would need `blocks/blocks_1_4_2.m`,
which is not in the repository.

**`app4_v6_solution.nb`** (P-first; scratch cells without definitions of their own). This notebook holds an
exact rank-44 solution for U^T, n = 4, d = 2 in the P-first convention: register order P, O_1..O_4 | I_1..I_4, F,
with the left register in `elementary_1_4_2.m`. A 25-variable guess with values 1/12, 1/6 and ±1/2 (Choi rank 140)
is reduced to an SDP in a1..a25 (In[316]). Rounding that SDP's solution to multiples of 1/2 leaves nonzero blocks
only for μ = 3, with Choi rank 1·12 + 3·8 + 2·4 = 44 (Out[311]); the fidelity is exactly 1, though the notebook
does not print it. The notebook does not check feasibility, and the extra constraints in In[316] and the relations
`param2` are hand-derived. Requirements:
- The kernel of a v6 session with {p,q,d} = {4,1,2}, for `x[...]`, `irrepDims`, p, q and d.
- **`app4_data/eq_4_1_2_50_left.m`**, to check the solutions. They do not satisfy the P-last
  `eq_4_1_2_exact.m`, because there the variables mean something else.

**`app4_v7.nb`** (edited until March 2023; P-first like v6). Its one lasting product is
`app4_data/eq_4_1_2_50_left.m`, exported in In[69]. **Its objective is mis-paired.** It uses
Ω = Σ `KroneckerProduct[εLeft, shiftVec[ε]]` with M = G.Ω.G, whereas v6 uses shiftVec[ε] ⊗ ε with Gᵀ.Ωᵀ.G
(as `app4.nb` does with ε ⊗ ε). As a result, its (4,1,2) SDP, which has five extra hard-coded zero constraints and
ended in "Partial Success", reports 1.9438 (Out[306]). That is above 1 and impossible for a fidelity. Other
caveats:
- The visible parameter cell is {3,0,2} (U^{-1}, n = 2, d = 2), and no result for it is saved.
- The copied v5 guess cells are P-last and meaningless here: the guess violates 294 of the 672 `_left`
  constraints.
- Like v6, it needs `blocks/blocks_1_4_2.m` for (4,1,2).

**`bratteli_diagram.nb`** (Feb.–Mar. 2023). A Mathematica drawing of the Bratteli diagram of A^d_{p,q}:
- `BratteliLevels[p,q,d]` deletes the vertices removed by len λˡ + len λʳ ≤ d (Sect. 5.4).
- `OrderWBA` is the edge rule of Sect. 5.1.
- Vertices are drawn as pairs of Young diagrams.

It needs the third-party package GroupMath by R. M. Fonseca (version 1.1.2 was used). The notebook loads it with
`` <<GroupMath` `` only for `YoungDiagram`; loading it emits a `SetDelayed::write` message, which is saved in the
notebook. It reads and writes no
files, so it works from any folder. The saved run is {p,q,d} = {6,1,7}, which is not one of the paper's figures,
and Out[7]/Out[8] are stale, from (3,2,2). Paper parameters: Fig. 1 is {4,0,d} with d = 4, 3, 2; Fig. 2 is {2,2,d}
with d ≥ 4; Fig. 3 is {2,2,d} with d = 3, 2. `OrderWBA` has misplaced brackets: two `If`s get four arguments, and the test
`Total[x[[1]]]<=x[[3]] && Total[y[[1]]]<y[[3]]` gets no False branch, so it returns `Null` instead of `False`. This does
no harm, because `RelationGraph` only draws an edge when the rule returns `True`. The repository's figure source is the Sage notebook, which marks removed edges
in red instead of deleting vertices.

## Data: `app4_data/`

All three files hold the 672 linear constraints of the U^T, n = 4, d = 2 comb SDP: entry 1 is Tr C = d^5 = 32,
followed by the comb conditions (172) for i = 1, …, 5. For i ≥ 3 these are mapped to irreducible blocks. The
variables follow the naming `xλμ` plus the sorted pairs (ik, jl). The P-last reference version is
`app4_data/eq_4_1_2_exact.m` in the repository root.

**`eq_4_1_2.m`.** The P-last constraints in machine precision. They agree with `eq_4_1_2_exact.m` to 9e-16 and match
the output of v5's constraint cell. No notebook reads this file, and none of the notebooks here writes it.

**`eq_4_1_2_50.m`.** The P-last constraints at about 50 digits. They agree with `eq_4_1_2_exact.m` to about 1e-55, i.e. to their working precision. The
file comes from a version that is not in the repository, and no notebook reads it.

**`eq_4_1_2_50_left.m`.** The P-first constraints, written by `app4_v7.nb` (In[69]) and read by it (In[278]). They
differ from the P-last files in 670 of 672 entries: only the trace constraint and the identically zero entry
coincide. Use this file only with the εLeft ⊗ ε variables of v6/v7, for example to check the solutions in
`app4_v6_solution.nb`. Never use it with `guessAnsatz` or with the variables of `app4.nb`.
