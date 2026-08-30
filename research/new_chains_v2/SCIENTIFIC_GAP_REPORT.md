# Scientific gap report after refactor

## Closed code/semantic gaps

1. Added typed relation target semantics (`primitive_isolated`, `feasible_kappa_response`, `product_surrogate`).
2. Added explicit natural/frozen/transported history-target semantics.
3. Existing conditional AIPW now fails closed outside natural `P(W|X)` targeting.
4. Added gauge-invariant component error `delta_circ` and radius-stability code.
5. Added exact support-deficit identity, zeta_def/2, E/2, LP and support-bracket code.
6. Added `Omega^- / Omega^+` objective and projected-span brackets.
7. Added general finite conditional `kappa`, isolation `chi`, TV bound and near-additive `rho`.
8. Added abstract sharp and operational PAIRWISE score-to-decision transfer.
9. Added product-reference surrogate as a separate semantic route.
10. Added finite reference-fidelity characterization search based on complement marginal invariance.
11. Added clone-state joint-response oracle adapter for actual environments.
12. Added F3 paired-shadow interface with explicit target-key changes.
13. Missing/unfitted H1 metrics no longer collapse to zero; DR telemetry semantics are separated from protocol integrity.

## Remaining scientific work, not implementation bugs

- Lean formalization of new theorems.
- Prove or refute a stronger support-rankability iff characterization beyond exhaustive small worlds.
- Construct statistically valid support brackets from logged trajectories.
- Convert oracle/realized error terms into simultaneous high-probability bounds.
- Implement/validate a learned CIG-AMF F3 shadow adapter if F3 is pursued.
- Integrate frozen `nu*` standardization with learned history-level nuisance predictions in the main MARL development runner.
- Build query-specific acquisition on shared neural-response covariance rather than claiming independent-head Neyman allocation is final.
