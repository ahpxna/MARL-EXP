# Our results against the closest literature, and the experiments they point to (02/10/2026 00:5x EDT)

User 00:5x: research with what we have (CPU full): novelty / breakthrough, new papers, new search angles, and the points
where our results suggest experiments.  Abstract-level reads unless noted; not exhaustive.

## Result-by-result
| Our result (ledger) | Closest work | What is already known there | What ours adds / differs | Experiment it points to |
|---|---|---|---|---|
| Channel-forced region: at constant K = 1 no scheduler keeps the learned receiver positive; floor proved (L-224…L-242) | Farazi–Klein–Brown (AoI lower bounds, every schedule); Kaul–Yates–Gruteser (piggyback relay) | Counting bounds with ≤ ν transmitters, one status per packet | Prefix decoding with self-exclusion (K, not K + 1), full-table relay, heterogeneous Σ K*; used as a predicate for a LEARNED receiver | 4×4 const K (pending, Addendum 4) |
| Value tracks the COUNT of out-of-range copies, not their summed age (L-239, L-240: ρ +0.983; 6/6 prospective hold cells) | Cho & Garcia-Molina 2000 ("freshness" = fraction up to date vs "age"; different optimal policies); binary freshness (Bastopcu–Ulukus); Ahmed–Ghosh–Wang–Shroff 2026 (arXiv 2603.26998: information EXPIRES, doubly-thresholded scheduling, +50 % over age-based) | Count / expiry metrics beat age for some objectives; expiry from plant dynamics | The expiry threshold is the receiver's TRAINING age range (H-C), measured, not modelled; bounded by our floor; predicts the sign vs a strong silent comparator | E3 (heterogeneous budgets), E2 (expiry by sender volatility) |
| The learned error-vs-age curve follows the training age distribution (H-C, L-237) | Shisher & Sun 2404.16281 (non-monotone e(δ), AoI as input; assumes e(δ) transfers regardless of the deployment AoI); co-design 2308.10094 | Non-monotonicity from non-Markov data | Non-monotonicity from TRAINING SUPPORT; peak moves 1–2 → 3–4 when the training channel changes | E1 (mismatch law) |
| Band: a K = 1-trained receiver loses its advantage when the channel improves (interim TM3, 4/4 seeds, L-238) | Network-aware training (CALF, arXiv 2603.12543); low-bandwidth mismatch and dropout training (CTHE/MARO, 2210.06274); delay mismatch in Smith predictors (both directions degrade) | Training under the deployment network helps; under-provisioned channels hurt untrained policies; in model-based control a delay mismatch in EITHER direction hurts | The "upgrade hurts" direction for LEARNED communication with return-level evidence; the learned receiver behaves like a dead-time compensator tuned to its training channel | E1 (both-sided mismatch law) |
| Stale messages can be worse than none | CAIC (UAI 2026), DACOM (AAAI 2023), SyncNet (ECCV 2022), AgentComm-Bench (2603.20285) | Documented, repaired empirically | Explained and predicted (forced vs scheduler-induced) | — |
| Scheduler repair is impossible at K ≤ 2 for this coordinate (count-deadline reduces the count by exactly 0; L-240) | Expiry-aware scheduling (2603.26998), earlier deadline head (ours, L-178) | Expiry-aware scheduling gains when the channel has slack | Where the floor binds no scheduler can gain; gains only where the floor is loose (here ≤ 0.5 copies) | E3 (find channels with slack) |
| Information measured by the TEACHER predicts cell-level returns; the STUDENT's acceptability does not predict trajectory returns (L-236, L-239, H6) | VoI of messages (VIL2C), I2C necessity labels | Decision-level VoI used to schedule | Methodological: info-side measures are reliable at cell level; student-side decision proxies on d^R are not | — |
| Shared per-student quality (ρ −0.818; relayCK1 K1 vs iid ρ 1.0, n = 4) | Seed variance in deep RL | Large seed effects | A student-level axis orthogonal to the channel axis | E5 (cheap pre-deployment probe) |

## Verdict
- Every ingredient has a neighbour (count / expiry freshness, AoI-aware learned inference, network-aware training,
  stale-worse-than-none, AoI lower bounds, delay-mismatch control).  None found combines them, and three claims were not
  found anywhere: (1) for learned receivers the relevant freshness is relative to the TRAINING age distribution, giving a
  band in which better channels can hurt (return-level evidence); (2) a channel-only, theorem-bounded count coordinate that
  predicts the sign of communication value against a strong silent comparator, out of sample, with a closed-form
  provisioning rule; (3) a scheduler-impossibility result separating scheduler-repairable from receiver-repair-required
  regimes.
- Breakthrough level: a strong "understanding + design rule" paper, not a new algorithm.  It becomes a notable result if
  the 4×4 cells confirm the training-relative prediction (prospective) and the mismatch law (E1) holds on both sides.

## Experiments the results point to (ranked by value / CPU)
- E1 (eval-only, ≈ 20 min on one core): the both-sided MISMATCH LAW.  Deploy relayCK1 (K = 1-trained) at const K = 2, 3 and
  use the existing const-K / iid cells of both students; x = a channel-only distance between the deployment and the training
  age histograms (e.g. Wasserstein-1), y = gain vs Z.  Prediction: gain falls with the distance on BOTH sides of the
  training channel (the Smith-predictor analogue).  Needs a protocol and an unused panel.
- E3 (channel-only, minutes): heterogeneous budgets — net with the Σ K* floor for rich7, bursty, high, low; compare with the
  known rich7 / low / cap4 gains (another out-of-sample check, and a search for channels with scheduler slack).
- E2 (analysis only): weight stale copies by sender volatility (expiry from dynamics, as in 2603.26998) using the
  staleness-meaning probe's true states; does it reduce the residual ranking errors?
- E5 (analysis + small probe): a pre-deployment per-student robustness score (age-relabel acceptability on target-channel
  states) predicting the per-seed gain; partial evidence ρ 0.455–0.8.
- E4 (training, ≈ 30 core-hours, later): mixed-channel training to widen the band (draft protocol).

## Addendum 01:2x — two more angles
- RL with delays (Derman et al.-style random delays, arXiv 2010.02966; "Delays in RL" 2309.11096; survey 2602.00399): the
  focus is training under a given delay process; cross-delay transfer to a SMALLER delay (our "upgrade hurts") is not
  reported in the abstracts read — supports the novelty of the band claim; the mismatch-law test (E1, running) is the
  direct evidence.
- LLM multi-agent systems: "stale propagation" through shared memory is named as a distinct failure mode (Governed Shared
  Memory, arXiv 2606.24535; inter-agent misalignment ≈ 37 % of failures in production audits) — an application where the
  count-of-out-of-support-entries view and the provisioning rule could transfer; not pursued here.
