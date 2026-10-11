# Independent verification scripts

Pure-Python re-implementation (no Sage, no Mathematica) used to check the idempotent database and
the numbers reported in Grinko & Ozols, *Linear Programming with Unitary-Equivariant Constraints*,
Commun. Math. Phys. 405, 278 (2024). See `../REVIEW.md` for the findings.

Requirements: `numpy scipy sympy cvxpy` (the SDPs use the Clarabel solver shipped with cvxpy).

| script | what it checks | runtime |
|---|---|---|
| `wb.py` | walled Brauer algebra engine (diagrams, products, traces, JM elements, contents, DB parser) | – |
| `verify_db.py` | every file in `wba_idempotents_db/`: path set, `sum eps_T = 1`, `J_k eps_T = eps_T J_k = c_T(k) eps_T`, distinct contents, `Tr eps_T = dim` of the U(d) irrep, `eps_T^2 = eps_T` (numeric `d`: all identities checked after applying `psi_d`, exactly mod a prime) | ~25 min |
| `tables.py` | Tables 4, 5, 6, 7 of Appendix E (Table 5 via character theory, independent of the paper's eq. (200)) | ~1 min |
| `app1_check.py` | Sect. 7.1 / Example 7.1, `p^n_{2,2}(c)` for `n = 1..8`, exact (sympy) | ~1 min |
| `app2_check.py` | Sect. 7.2 majority vote: GT-basis LP and an unrestricted SDP on the full Choi matrix (`d = 2, 3`) | ~1 min |
| `app2_diag.py` | Sect. 7.2 LP (158) diagrammatically for `d` up to 100; the notebook's and a corrected closed-form solution | ~1 min |
| `app3_check.py` | Sect. 7.3, Examples 7.2/7.3: support function of the paper's block SDP vs. a direct SDP on the full Choi matrix | ~2 min |
| `app3_basis_test.py` | shows that the block extraction used in `app3.nb` depends on the choice of eigenvectors | ~1 min |
| `table2_check.py` | Sect. 7.4, Table 2 (all 16 entries), symmetry-reduced comb SDP | ~minutes (n=4, d=3 is the slowest) |
| `nb2txt.py` | converts the Mathematica `.nb` files to readable plain text (`python3 nb2txt.py ../app2.nb`) | – |

Run from this directory, e.g. `python3 verify_db.py`, `python3 table2_check.py transpose:3:3`.
