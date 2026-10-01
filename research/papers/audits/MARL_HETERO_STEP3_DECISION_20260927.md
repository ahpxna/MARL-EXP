# Heterogeneous broadcast: independent decision for Step 3

## Decision

GO for implementation and a small, staged learnability pilot on the heterogeneous-receiver objective. NOT an approval for a blind 768–1,000-context run, large actor training, a same-byte performance claim, or a publication-readiness claim.

The bounded-repair mechanism now has positive oracle evidence. The next uncertainty is whether a legal-information selector can exploit it at a useful cost. Freeze the present negative global-budget results and positive heterogeneous-oracle results; do not rewrite them to imply a learned result.

No training or traffic rollout was launched for this audit. Existing records were reaggregated. Small synthetic enumeration checks were used to check the search implementation, not to claim traffic performance. No producer or historical artifact was edited.

## What passed

Inspected the full exact producer, protocol, result report, analysis script, v3 trainer and its tests, and the relevant actor/environment methods. The exact collector's record hash and all recorded source hashes match the current files. The v3 report/decision hash and source hashes also match.

Exact artifact: `research/marl_budget/hetero_exact_20260927_173902/`.
32 snapshots (t=19,31), 16 episodes, 8 traffic seed IDs at two loads, 256 evaluation capacity vectors. No case was dropped by the product cap. All saved private/patched subsets passed cardinality, self-exclusion and radius checks on independent reaggregation; the stated byte formula matches saved byte counts. Maximum action-profile product was 2,304.

An independent m=4 brute-force comparison checked 1,944 permutation/capacity values and 648 bounded/private profile optima against direct subset-product enumeration. Noncontiguous phase IDs and the base=1 case also passed. This supports the correctness of permutation encoding, prefix masks and value-preserving action deduplication for the stated fixed actor and value functional.

| Quantity | Mean across this balanced panel |
|---|---:|
| advance R1 minus advance R0 | 8.453125 |
| advance R2 minus advance R0 | 9.621094 |
| private minus advance R0 | 9.621094 |
| known-budget best shared minus advance R0 | 6.863281 |
| private minus known-budget best shared | 2.757813 |
| extra bytes of advance R1 over R0 | 15.652344 |

R1 recovers 87.86% of the private-minus-advance-R0 gap; episode means are positive in all 16 episodes, satisfying the declared screening rule. R2 equals the private value in all 256 cases. These are panel observations, not universal radius theorems.

Crucially, private beats the EXACT known-budget best shared order in 106/256 cases. This comparison removes the old heuristic-search confound. The private-minus-known gap is positive at both snapshot times (means 2.148438 and 3.367188). That is sufficient evidence to investigate the mechanism further.

The 16 episodes have eight seed IDs at two loads. Neither 256 capacity draws nor three network initialisations creates that many independent traffic environments.

## Corrections to the new report

1. `pi_adv` is the exact maximiser of the empirical average over EIGHT capacity vectors at a fixed oracle snapshot. It is not certified optimal for the uniform distribution on all 7^9 vectors. `adv` means advance, not adversarial: the objective is an average, not a worst-case capacity objective. K_eval does not influence selection; that timing fix is correct.
2. Therefore `known_shared - adv_R0` includes finite-training-capacity estimation/tie-selection loss as well as the cost of committing before reveal. Do not call 6.86 the exact population price of timing.
3. R1 beats known_shared on average, but is worse in 11/256 cases (better in 84, tied in 161). Replace “removes the cost” with the measured average statement.
4. R=1 is per receiver. The saved R1 solutions use 1.34375 replacements in total on average, up to four on this panel; the admissible network-wide maximum is nine. This is not a one-packet correction for the whole network.
5. Byte arithmetic is exact for the declared canonical witnesses; their byte efficiency is not optimised. Every positive R1-over-R0 value gain in the panel uses additional accounted bytes. This does not establish an equal-cost advantage.
6. Protocol canonical tie-breaking says (fewest replacements, fewest senders outside prefix, smallest mask). `feasible` uses only (replacements, mask). Either correct that sentence or change a future producer. The mismatch does not invalidate value exactness, but it matters if interpreting bytes as the protocol's stated tie-break.
7. The cap could create selection bias if future cases are excluded. It affected none of these results. Future summaries should return INCOMPLETE rather than a full-panel verdict when preregistered cases are missing.

The new v3 trainer fixes the important holdout-label normalisation issue and saves raw selections, hashes, and paired-budget evaluation. Raw saved selected-set values/regrets were checked against the original tables (155,520 records; no inconsistency). Its tests include a positive control. This is progress, not a reason to rerun the old training again.

## Mandatory implementation contract for Step 3

### A. Legal information and timing

Let z be the scheduler's paid packet cache and public time/topology. Before reveal, compute pi(z). After reveal, compute S_hat(z,pi,K,B) using a learned evaluator. K may enter repair but not preparation. Fresh packets, actual joint actions, true f, oracle per-receiver attainable-action lists and optimal orders may label offline data but must not enter the deployed selector.

Add assertions/tests:
- Changing K or hidden current state at fixed z does not alter the prepared order.
- Changing oracle labels does not alter an inference call.
- Every selected S_i excludes i, has size k_i, meets its R limit and the declared byte budget.
- The received subset produces the same actor action in a live protocol step as its diagnostic counterfactual view, with the same old cache.

The old environment retains previously received packets not refreshed in S_i. State this explicitly; actors use their own observation, old cache, and the selected fresh updates. The new heterogeneous transport must update each receiver's cache only for packets actually decoded. The public scheduler's cache access must also be defined and charged consistently.

### B. Do not copy oracle action deduplication into the learner

The oracle reads current payloads to construct every receiver's mask-to-action lookup. That is why it can search a small product of phase sets. A public scheduler cannot construct this lookup before acquiring the messages.

For m=9 and k_i=4, each receiver's R1 family has 1 + 4*4 = 17 masks, so the full joint candidate family has 17^9 = 118,587,876,497 profiles. Do not promise complete candidate enumeration or zero search error in the deployed implementation.

Use a bounded, deterministic candidate generator, e.g. sequential receiver updates or a beam, scored only by f_hat(z,S). Include the unchanged base profile, fix tie-breaking, log evaluator calls, and benchmark search error against the exact oracle on the small diagnostic panel. Give the direct budget-aware baseline the same information, labels and search/evaluation allowance. A local search is not an exact solver.

For the first learnability pilot, keep the public heuristic base order fixed. This isolates whether learned repair can exploit known headroom. Only after this works add a learned shared order; otherwise errors of ranking, critic and repair search become inseparable again.

### C. Same-cost evaluation requires a cost-aware candidate search

Current code maximises value first and then reports bytes for one representative. That cannot compute max value subject to a byte cap. Equal-action sets may use different senders and have different union costs across receivers. In a synthetic four-receiver check of the current routine, the canonical private optimum used 83 bytes although another profile with identical optimal value used 58 bytes.

Do not retain only one mask per receiver/phase when constructing a cost-aware oracle. Retain the relevant alternatives and solve shared union coverage jointly, or retain a Pareto state containing the union mask and replacement count. The rollout value can still be cached by joint action, while subset realisations remain separate for cost.

For the pilot, implement the declared byte function and reject infeasible candidate profiles before selecting among them. Predeclare byte caps or a cost sweep without tuning to evaluation gains. Compare prefix, bounded repair and direct budget-aware selection under the same available resources. At low caps, report infeasibility rather than changing k_i or dropping rows silently.

If using the current idealised model, call the axis “accounted payload/control bytes”. There is no measured wireless airtime, loss or instruction latency yet. The omitted common schedule header must truly be identical across methods; otherwise include it. Patches are specified before transmission, so removed packets need not be decoded; already-broadcast bytes remain charged.

### D. Train on the heterogeneous objective, not the old global subset table

The target is joint f_x(S_1,...,S_m), not f_x(S) for one set broadcast identically to everybody. A model can consume z, K and a 9x9 binary receiver-sender selection matrix (diagonal zero). Keep IDs/topology available consistently across all methods.

Start with:
- public heuristic + no repair;
- same heuristic + learned R1 repair;
- direct budget-aware profile selection;
- oracle R1 and private solutions as explicitly privileged references.

Use the same training contexts and labelled rollout budget. Try public information first and privileged current summaries as a separate diagnostic. Do not describe those summaries as a full-state ceiling. Do not introduce paid bids until their actual traffic is implemented.

The current exact record file is a mechanism summary, not a ready training dataset: it saves winning profiles/values but no legal scheduler context or full mask-to-action/value tables. Replay/collect a small proper dataset; do not reconstruct hidden features from the optimal outputs. Save z before diagnostics, K, candidate profile, return, split, provenance, and raw decisions/checkpoints.

## Practical schedule and stop rule

1. Implement A–D and validate with small deterministic cases plus one live protocol smoke. Do not expand data while changing the feature/cost contract.
2. Collect a first 96-context pilot on new, independent traffic seeds. Keep validation/test seed IDs separate; save fixed data splits. The old exploratory panel is development data.
3. Compare learned R1 with its OWN no-repair base and the direct comparator, under matched costs. Inspect paired seed/episode results, per-capacity patterns, train/validation error and search error. No guarantee of a positive result is assumed.
4. If learning curves and validation improve, expand to 192, then 384/768 as justified. Increase independent seeds, not just density along the same trajectories. Choose progression with validation; reserve an untouched test panel for final evaluation rather than consulting it at every stage.
5. If the critic only memorises, diagnose representation/optimisation/search before more collection. A cutoff is a deadline/resource decision, not proof that the problem is unlearnable.
6. Train learned actors and evaluate closed-loop only after legal-information selection shows a useful signal. Frozen MP2 selector fitting is not yet a MARL learning result.

## Theory connection without blocking the pilot

T1 as inspected is a SINGLE k-subset theorem with one global R and a top-k score hypothesis. The heterogeneous problem is a product of per-receiver k_i-subsets with per-receiver radii and a joint, coupled rollout objective. Do not cite T1 as already instantiated by changing the name of R or adding receiver losses.

An immediate, valid finite-search statement is available for this actual profile space. Let F_{R,B}(pi,K) be the legal, byte-feasible profiles; V_{R,B}=max_F f; C subset F be the searched candidates, containing the returned S_hat. If
- |f_hat(S)-f(S)| <= epsilon on C;
- max_C f_hat - f_hat(S_hat) <= nu;
- V_{R,B} - max_C f <= zeta;
then
    V_{R,B} - f(S_hat) <= 2*epsilon + nu + zeta.

This separates evaluator error from search/coverage error without falsely claiming full enumeration. It is a standard finite-optimisation bound, not a novelty claim, and does not certify epsilon from mean test MSE. The additional structural term against the private optimum is private_value - V_{R,B}. A geometric T1 extension requires a blockwise exchange argument and its own hypotheses; leave that formal bridge explicit while collecting the pilot.

## Final go/no-go

The mechanism passes its original oracle screening criterion. Proceed with Step 3 implementation and the small pilot above. The essential next deliverable is a LEGAL selector and a cost-accounted comparison, not another claim that the oracle proves learned performance. No new literature search, broad simulator expansion or full-gate work is needed to make this decision.
