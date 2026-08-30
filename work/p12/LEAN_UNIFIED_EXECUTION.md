# Lean unified chains V4 — execution status

**Status: EXECUTED_WITH_LEAN_4_AND_MATHLIB.**

The active V4 sources in this directory were freshly compiled on 2026-08-29
with Lean `4.34.0-rc2` and Mathlib commit
`1f495c611d05d2215058cd77c7897d625bc3b445`.  See the repository-root
`LEAN_EXECUTION_LEDGER.md` for source SHA256 values, commands, exit codes, and
the exact verified/pending target matrix.

Completed formalization order:

1. oscillation quotient/gauge lemmas;
2. exact radius import/reproof;
3. `d(T)=e_+(T)+e_-(T)`;
4. one-sided `zeta_def/2`;
5. global `E/2`;
6. gauge-invariant fixed-subset stability and `2 Delta_circ`;
7. lower-bound certificate implication;
8. support monotonicity and `Omega-/Omega+` regret bracket;
9. projected-span bracket;
10. oscillation-add deviation;
11. reference isolation bound and TV corollary;
12. complement-marginal-invariance reference-fidelity iff for all additive complement basis functions;
13. near-additive `rho <= 2 eta`;
14. sharp PAIRWISE theorem;
15. operational Gamma theorem;
16. exact top-k interval certification.

All eight active V4 modules compile with exit code 0. Static scan: zero
`sorry`, zero `admit`, zero user axiom. This status does not claim that pending
targets listed in the execution ledger are verified.
