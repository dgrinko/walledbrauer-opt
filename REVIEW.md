# Code review and independent verification

Scope: everything in this repository (`wba_tools.py`, the two Sage notebooks, `app1.nb`–`app3.nb`,
`wba_idempotents_db/`) checked against D. Grinko, M. Ozols, *Linear Programming with
Unitary-Equivariant Constraints*, Commun. Math. Phys. 405, 278 (2024).

Every number below was recomputed with code written from scratch (`review/`, pure Python with
numpy/scipy/sympy/cvxpy; no Sage, no Mathematica). In addition, `wba_tools.py` itself was run
under passagemath (Sage 10.8) to reproduce the database and to test individual functions.

## Verdict

* **The core method and the idempotent database are correct.** All 87 files in
  `wba_idempotents_db/` pass every check (see table below), and the repo's own generation code
  reproduces the stored files byte for byte.
* **The published numbers are correct**: Example 7.1, the value F = 8/9 in Sect. 7.2, the
  feasible regions of Examples 7.2/7.3 (Figs. 6/7), Tables 4–7 and all 16 entries of Table 2.
  The only error found in the paper is a typo in Table 7.
* **The application notebooks have real problems**, though, and do not establish some of the
  paper's claims as written. The most important ones:
  1. `app2.nb` (majority vote) does not solve the LP (158) given in the paper: the cell that
     defines the relation `f` overwrites the 3-rule version with the 2-rule version. The
     closed-form "general d" solution it prints **violates the `123 -> {1,2,3}` constraint of
     (158) for every d >= 9**. The optimum is still 8/9; a corrected closed form is given below.
  2. `app3.nb` (cloning) builds the Schur-basis blocks from independently chosen eigenvectors of
     each primitive idempotent. That is only valid if those bases happen to be aligned, and nothing
     checks it. With a different (equally valid) choice the extracted blocks give a wildly wrong
     region. The published formulas (160)–(169) are nevertheless correct (verified).
  3. The notebook for Sect. 7.4 / Table 2 is not in the repository, although the paper says it
     is on GitHub [GO22].
  4. `app2.nb` and `app3.nb` load from `./idempotents_db/`, but the folder is
     `wba_idempotents_db/`, so neither notebook runs as shipped.

## Verification results

| Item (paper) | Independent result | Status |
|---|---|---|
| DB: 27 symbolic files `primitive_p_q.txt` (generic z) | path set = Bratteli paths; Σ ε_T = 1; J_k ε_T = ε_T J_k = c_T(k) ε_T with J_k from eq. (85) and contents from Sect. 5.3; contents distinct; Tr ε_T = Weyl dimension of λ; ε_T² = ε_T (p+q ≤ 5) | all pass |
| DB: 60 numeric files `primitive_p_q_d.txt` (d < p+q) | same identities after applying ψ_d (exact, on random vectors mod 2³¹−1); path set = truncated Bratteli diagram (len λˡ + len λʳ ≤ d) | all pass |
| DB: every stored diagram is a walled Brauer diagram | 28,496 distinct diagrams | pass |
| DB reproducibility | `generate_walled_brauer_idempotents.ipynb` (under passagemath) regenerates the files byte for byte (12 files tested) | pass |
| Table 3, 4, 5, 6, 7 | recomputed (Table 5 via characters: n = Σ_{α⊢p,β⊢q} z_α⁻¹z_β⁻¹ Σ_{λ⊢p+q, len λ≤d} χ^λ(α∪β)², independent of eq. (200)) | all entries match; **typo**: Table 7, p+q = 9, d = 8 reads "3,62,879", should be 362,879 |
| Example 7.1, eq. (152) | exact symbolic recomputation | identical; c₁ = 0.821569391, c₂ = 0.913830846, p³(c₂) = 0.566968021; n = 1 bound (153) and minimum 1/2 at 1/2 + 2^(−4/3) confirmed; n = 1..8 curves increase with n |
| Sect. 7.2, F = 8/9 | LP (158) with all three rules: 8/9 for every tested d (2–10, 12, 16, 20, 50, 100); unrestricted SDP on the full d⁴×d⁴ Choi matrix (no idempotents, no extra symmetry): 8/9 for d = 2, 3 | value correct; notebook issues below |
| Example 7.2 (d = 2), 7.3 (d = 3) | support function of the region defined by (160)–(169) vs. a direct SDP over the full Choi matrix, 42 directions | agree to ≤ 2·10⁻⁷; symmetric optimum 5/9 (d=2), 1/2 (d=3) = universal cloner |
| Table 2 (16 entries) | symmetry-reduced comb SDP, written independently (`review/table2_check.py`) | see Table 2 section below |

## Findings in the code

### 1. `app2.nb` (Sect. 7.2, quantum majority vote)

* **The relation actually optimised is not eq. (156).** Cell `In[25]` assigns `f` three times
  (`app2.nb` lines 510, 527, 550): first the d = 2 rules `{000→0, 001→0}`, then the d ≥ 3 rules
  that add `012 → {0,1,2}`, then the d = 2 rules again. The last assignment wins, so every saved
  result (`Out[272]`, `Out[295]`) is for the 2-rule LP, not the 3-rule LP (158) described in the paper.
* **The printed "General d solution" is infeasible for (158) when d ≥ 9.** For that solution
  (`a4 = (d−2)/((d−3)(d+1))`, `a5 = (d+2)/3`, `a8 = a9 = 2(d+1)/3`) I get, symbolically in d,
  F₁₁₁ = 1, F₁₁₂ = 8/9, **F₁₂₃ = (5d+8)/(6(d+1))**, which is < 8/9 for d ≥ 9 (and → 5/6).
  It was obtained with `FindSequenceFunction` from d = 5..12 without the third rule.
* **The optimal value 8/9 is still right.** With all three rules the LP optimum is 8/9 for every
  tested d (3–10, 12, 16, 20, 50, 100; `review/app2_check.py`, `review/app2_diag.py`), and the
  following closed form is feasible for all d ≥ 3, exactly (checked symbolically in d), with
  F = (1, 8/9, 1):

  | path (last edge) | weight |
  |---|---|
  | (3) → (2,∅) | (d+2)/3 |
  | (21) → (11,∅), both paths | 2(d+1)/3 |
  | (111) → (11,∅) | (d−2)/3 |
  | all others | 0 |

  At d = 3 this is exactly the "d = 3 solution" already written in the notebook, so it is the
  natural all-d formula. Since the 2-rule LP already has optimum 8/9, this proves F = 8/9 for
  (158) for every d at which the 2-rule optimum is 8/9 (tested here up to d = 100, in the notebook for d = 5..12).
* The d = 2 case claimed in the paper cannot be run: `symConstraints[2]` is never defined, and
  the trace-preservation constraint is imposed by matching diagram coefficients, which needs
  ψ_{3,0} to be faithful (d ≥ 3; the paper's own restriction (118)). I confirmed 8/9 at d = 2
  independently (LP with the trace constraint imposed on the actual matrices, and the full SDP).
* `symConstraints[3]` / `symConstraints[d]` are hard-coded indices. I checked that they match
  the path order in `primitive_3_1_3.txt` / `primitive_3_1.txt`, but they would silently break
  if the database were regenerated in a different order. Generate them from the path labels instead.

### 2. `app3.nb` (Sect. 7.3, asymmetric cloning)

* **Basis alignment is assumed, not enforced.** `U = Join@@(Vecs/@Πs)` (`app3.nb` ~line 753)
  takes an arbitrary orthonormal basis of the image of each primitive idempotent separately
  (`Eigensystem` + `Orthogonalize`, line ~390), and `Blocks` (line 498) reads block λ off the
  first vector of every path. This gives the true block X_λ only if the bases for different
  paths T, T′ with the same leaf are related by the matrix units ε_{TT′}; otherwise one gets
  X_λ ∘ G (Hadamard product with a Gram matrix), a strictly weaker positivity constraint.
  `review/app3_basis_test.py` repeats the d = 2 computation: with aligned vectors it reproduces
  the true region exactly, with random orthonormal vectors the "region" becomes
  max(p₁+p₂+p₃) = 2.53 or 7.42 instead of 5/3, i.e. clone fidelities above 1.
  The published d = 2, 3 formulas are correct (verified against the direct SDP), so Mathematica's
  canonical null-space vectors happened to be aligned here. Fix: align via the Appendix D recipe
  (ε₁ B ε_i), or use the cyclic submodule generated by one vector (as in `review/table2_check.py`),
  and at least test that `P.U.M.Uᵀ.Pᵀ` really has the form ⊕ X_λ ⊗ I.
* The notebook state is not reproducible: cells were evaluated far out of order
  (`In[1066]`, `In[1165]`, `In[1156]`, `In[268]`, …), the `{p,q,d}` cell has no label, and saved
  outputs come from both d = 2 (`dB={1,3,2}`, `dU={5,3,1}`) and d = 3 runs (`Out[188]` has four blocks).
  `subst` and `spq` are used/defined across cells in an order that does not run top to bottom.
* `Off[SemidefiniteOptimization::…]` hides solver warnings during the region plots, and the
  partial trace uses `ResourceFunction["MatrixPartialTrace"]` (needs network access to the
  Wolfram Function Repository).

### 3. `wba_tools.py`

* **`psi_wb` cannot run**: `wba_tools.py:158` calls `vectorize_element`, which does not exist
  (`NameError`); it should be `vectorize_element_wb`. Only used in commented-out notebook code.
* **`psi_one_wb` builds the transpose of ψ.** Rows are indexed by the negative (bottom) labels and
  columns by the positive (top) labels (`wba_tools.py:151-153`), whereas eq. (44) has the top row as the
  bra. Since Sage's `a*b` puts `a` on top of `b` (checked), `psi_wb(a*b) = psi_wb(b)·psi_wb(a)`,
  i.e. it is an anti-homomorphism. Harmless for the stored idempotents (they are flip-symmetric),
  wrong for general elements. `app3.nb`'s `ψ` (`ketbra[in, ip, …]`) uses the same transposed
  convention, again harmless there because only idempotents and a generic Hermitian combination are mapped.
  `psi_one_wb` also ignores its `K` argument (always `QQ`), and `index_range` is unused.
* **`jucys_murphy(1)` returns 0 when p = 0**, but eq. (85) gives J₁ = δ. The `+δ` term is set
  inside `for i in range(1, j)` (`wba_tools.py:113-114`), which is empty for j = 1. It has no
  effect on the database (that edge has a single child, so its interpolating polynomial is 1),
  but it is a latent bug. The local dict `d` also shadows the dimension `self.d` there.
* `lambda_mu_content` (`wba_tools.py:166-185`) silently returns `None` for an invalid edge when
  `level_p` is true (only the other branch raises).
* Numeric-d databases use the *untruncated* (family B) interpolating polynomials
  (`interpolating_polynomial_lambda_mu`, notebook cell 0) while eq. (96) of the paper says the product runs
  over edges of the truncated family A; `interpolating_polynomial_lambda_mu_d` is dead code. The two give
  the same image under ψ_d (the extra factors evaluate to 1 on the A-paths, and no denominator vanishes
  because len λˡ + len λʳ ≤ d). Verified numerically for every numeric file. Worth a comment in the code
  or a sentence in the paper (it matches eq. (246) of Appendix D).

### 4. Repository-level

* No README: nothing says which notebook belongs to which section, which Sage/Mathematica versions
  were used (SageMath 9.4, Mathematica 12.3 from the metadata), or that `app1` does not use the database
  (it hard-codes the traces Σ_λ c_λ f^λ s_λ(λ₀, λ₁) in `pData`; all eight are correct).
* Sect. 7.4 (Table 2) code is missing.
* `generate_walled_brauer_idempotents.ipynb` cell 4 loops to p+q = 7, but its saved output ends in a
  `KeyboardInterrupt` at (p,q) = (1,3), and the repository contains p+q ≤ 6 only.
* `bratelli_diagram_walled_brauer.ipynb` depends on the third-party `slabbe` package and shadows the
  builtin `ord`.

## Readability suggestions (`wba_tools.py`, notebooks)

* Merge the `_d` duplicates (`walled_brauer_irreducibles[_d]`, `bratteli_antecedents[_d]`,
  `bratteli_descendants[_d]`, `gelfand_tsetlin_basis[_d]`, `interpolating_polynomial_lambda_mu[_d]`)
  into one function with `d=None`.
* Define the walled-pairing predicate once (it is written out twice, lines 17-20 and 31-34).
* Remove dead code: the half-integer branch of `WalledBrauerDiagrams.__init__` (copied from
  `BrauerDiagrams`; walled Brauer orders are always integers), `interpolating_polynomial_lambda_mu_d`,
  the unused `index_range`.
* Replace `from sage.combinat.diagram_algebras import *` by explicit imports, and add docstrings that
  state conventions: which row is "top", the product order, the content rule and the JM formula
  (with equation numbers of the paper).
* In the generation notebook: hoist `jucys_murphy(k+1)` out of the inner loop (it is recomputed per
  edge), pass an explicit `symbolic=True` flag instead of comparing `d == var('z')`, use `with open(...)`,
  and don't shadow `file`.
* Exchange data with Mathematica in a structured format (JSON, or a Mathematica-readable dump)
  instead of re-parsing Sage's `str()` output with string substitutions (`Parse` in `app2.nb`/`app3.nb`),
  which breaks if Sage changes its printing.
* Typos in Mathematica comments: "Pares", "Rmove", "curcly", "eingevectors".

## Table 2

Table 2 is reproduced with an independent, symmetry-reduced formulation (`review/table2_check.py`):
C is expanded in walled Brauer diagrams of B_{n,1} ⊗ B_{n,1} (transposition) or
B_{n+1,0} ⊗ B_{n+1,0} (inversion), all (partial) traces are diagrammatic, operator equalities are
imposed through Hilbert–Schmidt inner products (valid also for d < p+q where ψ_d is not faithful),
and positivity is imposed on the compression of C to V_λ ⊗ V_μ, using the cyclic submodule generated
by a single vector (so no basis alignment is needed). The fidelity is (1/d²) Tr[C X_I] with X_I
the product of maximally entangled projectors on I_i O_i and P F, which equals the Haar average for
covariant C.

| f(U) | d | n = 1 | n = 2 | n = 3 | n = 4 |
|---|---|---|---|---|---|
| Uᵀ | 2 | 0.500000 ✓ | 0.750000 ✓ | 0.933013 ✓ | PENDING |
| Uᵀ | 3 | 0.222222 ✓ | 0.407407 ✓ | PENDING | PENDING |
| U⁻¹ | 2 | 0.500000 ✓ | 0.750000 ✓ | 0.933013 ✓ | PENDING |
| U⁻¹ | 3 | 0.222222 ✓ | 0.333333 ✓ | PENDING | PENDING |

(✓ = equal to the paper's value to all 6 printed digits.) For d = 2 the two rows must coincide,
since for U ∈ SU(2) one has Uᵀ = σ_y U⁻¹ σ_y up to a phase, so qubit transposition and inversion are
equivalent tasks; the paper's "new" d = 2, n = 4 transposition result therefore also follows from
the exact qubit inversion protocol of [YSM22].

## Reproducing

See `review/README.md`. Main commands (from `review/`): `python3 verify_db.py`, `python3 tables.py`,
`python3 app1_check.py`, `python3 app2_diag.py`, `python3 app3_check.py`, `python3 table2_check.py`.
