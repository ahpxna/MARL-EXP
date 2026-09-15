# Adaptive continuation: precise scope

The original immediate assignment (steps 1–4) was completed in `research/d05_d06_worker_acceptance_20260912`. This continuation addresses the later adaptive obligations. It does **not** establish the full expected-stopping Gamma theorem.

## Proved constructions in this continuation

- `LeanFiniteTrackerCausalityV1`: the existing concrete tracker is prefix causal. Its fixed finite choice is measurable; its counts and next query are adapted when the current targets are adapted. The query at index N uses targets through index N, hence is selected before observation N+1.
- `LeanFiniteGridSolverV1`: finite simplex grid, fixed tie selection, measurable finite optimization, and L1 grid approximation. For H>0 and a simplex objective with one-sided L1 modulus C, optimization error is at most C d²/H. No optimizer-quality assumption appears in the returned solver theorem.
- `LeanD6FiniteGridAllocationV1`: actual legal D6 information objective. Every finite legal allocation pads with zeros into the full finite library E. Consequently library loss relative to the original `oracleValue` is zero. Error is cap(q)|E|²/H, where cap(q)=(q+2)²/2. The A07 bound uses the proved tolerance.
- `LeanQuadraticIntervalMinimumV1` and `LeanD6FiniteNuisanceEvaluationV1`: exact nuisance minimization on [0,1], including zero curvature, followed by a finite minimum over alternative labels. This equals the original sInf allocation value for legal nonnegative weights.
- `LeanD6FiniteSolverToleranceV1`: for eps>0, choose H=ceil(cap(q)d²/eps)+1. The solver meets eps. Replacing the grid objective by the finite quadratic evaluator returns exactly the same weights, including ties.
- `LeanD6FiniteSolverMeasurabilityV1`: for q>=2, measurable world estimates in `worlds q j`, margin estimates in [0,1], and positive deterministic grid denominators give measurable actual target weights and an adapted concrete query process. The true label is not an input to the policy.
- `LeanD6AdaptiveLabelAccountingV1`: actual oracle regret is bounded by cap(q); wrong-label loss is retained in the good/bad split. Whole-epoch deployment contributes H_s cap(q) P(B_s). Doubling lengths and quarter-rate error probabilities have a finite geometric total. The generic statement initially uses lower integrals, without hiding an integrability premise.
- `LeanD6FiniteSolverExpectationV1`: any statistic of the returned finite grid point is measurable. For a probability measure, q>=2, true and reported worlds valid, true and estimated margins in [0,1], measurable estimates, and H>0, actual solver regret is integrable and its ordinary expectation satisfies the correct-label A07 term plus cap(q) P(wrong label). Feasibility and optimizer quality are supplied by the solver proofs.
- `LeanD6FiniteAdaptiveTrackingV1`: empirical weights are the frequencies of the same emitted queries. For N>0, the actual pathwise information regret is bounded by the average of good-label estimation/grid errors and bad-label cap(q), plus cap(q)|E|²/N. Discovery and cyclic acquisition queries are explicitly separate from these N exploitation queries. The complete library has cardinality at most (n+1)+2*2^(n+1).
- `LeanD6DiscoveryStoppingTimeV1`: first observed discovery acceptance is a stopping time for the natural filtration of completed-block score summaries. The event {first<=N} is exactly the finite union of acceptance events through N. Under the Gaussian mean identity and r0>=512, termination is almost sure and expected raw-query cost is finite. At first epoch s, the raw-query count is 4|I|r0*2^s, reusing observations from previous prefixes. This theorem concerns discovery, not the allocation likelihood stopping certificate.
- `LeanD6ActualDecoderAllocationV1`: the existing observation-only, world-valued decoder is measurable. For q>=3, a true world in `worlds q j`, a fixed feasible fallback, distinct anchor/helper indices and r0>=512, its error at r0(s+1) contrasts is bounded by eta*4^(-s) under the actual D6 legal-query Gaussian means. The full expected cost of H*2^s wrong-label deployments is bounded by 2*C*H*eta. No independence across epochs is assumed. The decoder is prefix causal. For valid returned worlds, geometric optimality of the returned complement is equivalent to exact label identification in this construction.

## Important retained assumptions and limits

The generic grid theorem requires nonnegative simplex weights and a proved modulus; the D6 instantiation discharges the latter using existing actual-information results. D6 comparison theorems retain j not in A, a nonempty admissible alternative set, legal queries, mu in [0,1], and the stated q lower bounds. World-valued applications discharge alternative existence through `world_has_alternative`. The physical D05/D06 stage retains the strong condition (q-1)b>=1.

The solver is an exact-real, finite mathematical construction with fixed classical tie selection. It is not a floating-point implementation or a polynomial-time algorithm. Both the full query library and the grid can be very large.

The finite-horizon tracker theorem allows arbitrary data-adapted estimates satisfying their stated domains. The actual decoder bridge discharges the label distribution, but a single acquisition schedule and clipped margin estimator are not yet wired into a complete transcript/update state.

## Remaining mathematical obligations

1. Instantiate one actual transcript with discovery, cyclic margin exploration, exploitation, state updates, and the likelihood certificate. Connect its observation filtration to all estimator and tracker proofs.
2. Prove almost-sure likelihood-certificate growth under identifiable worlds, then a summable tail for the **whole** stopping time. Discovery termination alone does not prove this.
3. Establish the expected Gamma leading coefficient with all query costs included; cyclic rounds cost 2q+1 queries. Show exploration overhead and checkpoint overshoot are negligible. An arbitrary dyadic stopping grid does not establish leading coefficient 1.
4. Establish a matching sequential change-of-measure lower bound for the same task and query cost if claiming optimality. The new `label_iff_geometry` establishes equivalence with the required geometric decision for this construction and valid world-valued outputs, but does not itself provide the sequential lower bound.
5. For growing q, control all finite terms, especially cap(q)|E_q|²/N. The displayed finite bound alone is not a useful uniform growing-dimension rate.

These are missing mathematical integrations/proofs, not merely pending Lean syntax fixes. No theorem in this receipt asserts them, and none is inserted as a hypothesis to claim completion.

## Verification

`manifest.json` is authoritative for accepted sources, compile exits, source/binary/log hashes, and theorem axiom audits. New-module receipts record recursive local source and compiled dependency hashes before compilation and verify that they remain unchanged afterward. Local dependencies are rebuilt from source in isolation, except for explicitly identified identical source/binary pairs reused from the previous verified acceptance receipt. The repository's pre-existing cached local binaries are not used for the final new-module build. Mathlib and toolchain provenance is recorded separately.
