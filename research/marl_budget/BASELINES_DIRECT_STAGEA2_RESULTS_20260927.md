# Closed-loop baselines, independently tuned direct selector, stage A v2, η correction (27/09/2026, 23:50)

- No ledger is edited. Nothing here is a preregistered confirmation unless stated.
- Setting everywhere: frozen MP2 actor, 3×3 CityFlow, `PROTOCOL_HETERO_v0` (i.i.d. capacities),
  total cap +84 B over the prefix bytes, bids charged.
- Independent recheck of this batch: `research/papers/audits/MARL_CRITICAL_PATH_INDEPENDENT_RECHECK_20260927.md`.
  Its four findings were verified against the code (§4, §5, §7). Three corrections are applied here.

## 1. Closed-loop comparison panel, fresh seeds 1101–1116 (32 episodes)

**Run.** `cl_baselines_20260927_232931`.
- Producer `MARL_hetero_closed_loop_v3.py`, hashes in its manifest, equal to the current files.
- Frozen B2 models from `b2_freeze_20260927/dev_map.json`.
- Descriptive; this panel was not preregistered.

**Corrected request baseline.** `cl_w2c_bin_20260927_234219`, producer `MARL_hetero_closed_loop_v4.py` (§4).

**Self-checks.**
- The report self-check passes: no deployable method used oracle access.
- The v4 prefix rows reproduce the v3 prefix rows exactly, 32/32.

Σ waiting and finished trips are paired relative changes against the prefix on the same episode.
Init seeds are averaged per episode, and the CI is a bootstrap over episodes.

| method | what it is | Σ waiting | finished | censored TT | bytes | edits/episode |
|---|---|---|---|---|---|---|
| prefix | cached-queue priority, R = 0 | — | — | — | 4893 | 0 |
| ctrl_history | frozen B2 control: direct selector, no bid | +0.18% [−0.30, +0.74] | +0.02% | +0.05% | +1.1% | 1.1–1.4 steps |
| **mlp_top2_joint** | **frozen B2 design: direct selector + 1 B bid** | **−0.28% [−1.65, +1.18]**; vs ctrl −0.47% [−1.65, +0.73] | −0.37% | −0.10% | +7.3% | **1.1–3.3 steps** |
| schednet_fresh | HEURISTIC: 1 B fresh own-queue weight per sender, sorted stream | **+4.70% [+2.09, +7.35]** (worse) | −3.58% [−6.20, −0.99] | +0.93% | +5.8% | 0 |
| where2comm_top2 (v3) | HEURISTIC request rule; **leaks the exact gap**, superseded | +0.39% [−1.57, +2.45] | +0.35% | +0.26% | +24.8% | 113 swaps |
| where2comm_top2_bin (v4) | the same rule on the declared 1 B bid only | +0.53% [−1.40, +2.53] | +0.43% | +0.26% | +24.8% | 113 swaps |
| oracle_heldphase | reference, not deployable | **−14.37% [−16.66, −12.02]** | +8.18% | −2.37% | +17.7% | 19.4 steps |

Units of "edits": for the learned methods and the oracle, the number of steps (out of 26) whose
profile differs from the prefix. For where2comm, the number of receiver swaps.

**Reading.**
1. The frozen B2 design again gives no closed-loop benefit, now on a second fresh panel. It edits in 1–3 of
   26 steps against 19 for the oracle. This is the same symptom as B3 (covariate shift, see
   `B3_CLOSED_LOOP_RESULTS_20260927.md`).
2. Neither heuristic communication baseline helps.
   - Ordering the stream by fresh own queue is WORSE than the cached-queue priority. A plausible
     cause, not tested: senders with low queues are never refreshed.
   - The request rule spends about 25% more bytes for nothing.
3. **Label.** Both baselines are heuristics inspired by SchedNet / Where2comm, not trained
   reproductions. They do NOT complete the critical path's "learned SchedNet adaptation", and they
   cannot support any claim against the published algorithms.

## 2. Independently tuned direct selector (development split 501–508, opened; not confirmatory)

**Runs.** `direct_indep_ctrl_20260927_233023` and `direct_indep_t2j_20260927_233023`.
- Producer `MARL_hetero_direct_indep_dev.py`: the epoch is selected with the direct metric at the
  +84 total cap, bid charged.
- Checked:
  - the wrapper reaches both trainers: `md.run_job` and `md.select_tau` are module globals;
  - `md.BID_BYTES['mlp_top2_joint'] = 10` is set before `run_job`;
  - the evaluation after `load_state_dict` is untouched.
- The selected epochs differ from the shared-critic runs:
  - ctrl: 11/39/23 against 27/39/27;
  - t2j: 7/3/27 against 3/7/35.

Mean gains over 384 development groups. Differences are paired, with a cluster bootstrap over episodes.

| cap | t2j shared R1 | t2j shared direct | **t2j indep direct** | ctrl indep direct | indep − shared (t2j direct) | **indep direct − shared R1** | t2j − ctrl (both indep direct) |
|---|---|---|---|---|---|---|---|
| +28 | +0.65 | +0.74 | +1.17 | +0.65 | +0.44 [+0.06, +0.90] | +0.52 [+0.18, +0.97] | +0.53 [−0.12, +1.18] |
| +56 | +1.39 | +2.50 | +2.51 | +1.01 | +0.01 [−0.69, +0.70] | **+1.12 [+0.25, +2.06]** | +1.50 [+0.29, +2.98] |
| +84 | +1.30 | +3.19 | +2.94 | +1.66 | −0.25 [−1.16, +0.61] | **+1.64 [+0.58, +2.88]** | **+1.28 [+0.11, +2.60]** |
| none | +1.26 | +3.15 | +2.77 | +1.67 | −0.38 [−1.30, +0.48] | +1.51 [+0.48, +2.73] | +1.10 [−0.09, +2.30] |

**Reading (development evidence).**
- Tuning the direct selector independently does not change the B2 operating point (+84). It helps
  only at +28.
- **Bounded repair R1 does not beat an independently tuned direct selector.** Direct is better by
  +1.1 to +1.6 (CI > 0) at +56, +84 and uncapped, and ties at +28. The best R1 variant (stage A
  v2, §3) is also not better: −0.04 at +28 and −0.68 [−2.12, +0.53] at +84.
- The paid-bid advantage survives independent tuning of both sides: +1.28 [+0.11, +2.60] at +84.
- **Consequence for the story.** In traffic, the supported statement is "a charged receiver-local
  bid helps a budget-conditioned (direct) selector in the held phase". It is NOT "limited revision
  R beats direct selection". This is the critical path's branch "if the budget-conditioned
  selector is as good or better", now observed for the heterogeneous protocol too.

## 3. Stage A v2, structural flip features (item 12; development only)

**Run.** `top2_joint_v2_dev_20260927_232700`. The producer `MARL_hetero_top2_joint_v2_dev.py` adds
four features per (candidate, receiver) from legal data:
- the bid;
- the scheduler cache z;
- the mirror;
- public coefficients in `mp2_coef_3x3.json`.

The z and mirror slot layouts were checked against `SchedulerContext.features` and `ReceiverMirror.features`.

**Stage A accuracy on the select split.**

| version | stage A | always-p1 |
|---|---|---|
| v2 | 0.7173 | 0.7093 |
| v1 | 0.7110 | 0.7093 |

This is a small classification difference.

**Critic, paired against v1 on the same groups.**

| cap | policy | v2 − v1 |
|---|---|---|
| +28 | direct | +0.61 [+0.13, +1.17] |
| +84 | repair_R1 | +0.96 [+0.17, +1.85] |
| +28 / +56 / none | repair_R1 | +0.48 to +0.87 (CI touches 0) |
| **+84** | **direct** | **−0.10 [−0.89, +0.64]** |

So v2 helps the restricted policy and the low cap, and not the B2 operating point.

**Not deployable as is.**
- The v2 stage A has 27 inputs.
- The closed-loop runners (v2, v3, latency) build the 23-input stage A.
- A new inference path plus a train/runtime parity check would be needed before any closed-loop
  test. None was run. B4 keeps the v1 checkpoints.

## 4. Correction: the request baseline leaked unencoded gap precision (verified)

- `MARL_hetero_closed_loop_v3.py:59–70` sorts the fragile receivers by the exact local MP2 gap. The
  declared bid carries only the 2-bit gapbin.
- The threshold itself (gap < 2 ⇔ gapbin ≤ 1) was equivalent; only the within-bin order leaked.
- **Fix.** `MARL_hetero_closed_loop_v4.py` (new file; v3 unchanged, its rows kept and labelled)
  orders by (gapbin, receiver id), a public deterministic tie rule, and asserts the threshold
  equivalence.
- **Effect.**
  - On seed 1101 the smoke run was identical.
  - On the full panel, 6 of 32 episodes change.
  - The mean moves from +0.39% to +0.53%. The conclusion is unchanged.

## 5. Correction: the η "bridge" is a one-swap local diagnostic, not a T1 certificate (verified)

- `MARL_hetero_eta_bridge.py` fits the additive model only to single-receiver one-swaps around P.
  Its η is a LOWER bound on the global ScoreLocal η, as its own docstring says.
- The field `frac_zero_price_certified` and the docstring phrase "keeping P_i is certified" are
  therefore wrong in wording. A lower bound cannot discharge T1's upper-error hypothesis.
- **Counterexample (recheck, checked by hand).** Take m = 4, k = 2, P = {0,1}, and f(S) = 1 iff
  {2,3} ⊆ S.
  - Every one-swap has gain 0, so the fit gives η = 0 and the margin test passes.
  - Swapping both items gains 1.
- **Correct labels** for `eta_bridge_20260927.json` (the JSON and the producer are unchanged):
  - "one-swap additive residual": 75.7% zero, p90 1.375;
  - "fitted local no-improvement": 63.3%;
  - the direct local statement, max one-swap gain ≤ 0: 72.5%, computed from the stored
    `best_swap` rows. The fitted condition implies it in all 15,631 cases, as it must.
- None of these closes the T1 → traffic bridge. That needs a valid UPPER bound for one consistent
  score vector over the relevant sets, or a theorem explicitly restricted to the one-swap
  neighbourhood.
- The earlier 82% figure in `MARL_STORY_VERDICT_20260927.md` comes from a different producer
  (`DIAG_cityflow_set_objective.py`). That producer uses exhaustive subset tables over physical
  neighbours, so it is not affected.

## 6. Fig 3 v3 and latency scope

- **Figure.** `figures_20260927_v3/fig3_closed_loop_cl_baselines_20260927_232931.png`, with a
  `.json` of the plotted numbers and the rows sha256.
  - Producer `scripts/MARL_make_fig3_v3.py`. It refuses to plot if a deployable row used the
    oracle, or if an extra run's prefix does not reproduce.
  - The where2comm row is the corrected v4 row; the leaky v3 row is dropped.
  - A first draft is archived in `legacy/fig3_v3_draft1_20260927/`.
- **Latency** (`latency_b2_20260927_232749/latency.json`, 208 steps):
  - scheduler median 16.6 ms, p95 17.9 ms, max 48 ms;
  - it is COMPUTE ONLY: no uplink round, no network delay, and delay does not act on traffic;
  - it was measured while three other training/evaluation jobs ran, so it is upward-biased.
  - 0% misses at 50 ms is not an end-to-end guarantee.
  - The heuristic baselines' latency is not measured.

## 7. Provenance supplement

- `PROVENANCE_SUPPLEMENT_20260927.json` records the sha256 of
  - the behaviour-changing wrappers (`MARL_hetero_top2_joint_v2_dev.py`,
    `MARL_hetero_direct_indep_dev.py`);
  - the coefficient JSON.

  None of these is in the runs' own manifests. Every file's mtime precedes its run dir's creation.
- The existing manifests are not rewritten.

## 8. Still pending

- **B4** (DAgger retraining, then the closed-loop test on 801–816). Controls are still training at
  23:50.
- **E3** (communication-aware learned actor): decided after the B4 verdict, as instructed.
- **Learned baselines.** A learned SchedNet / Where2comm adaptation needs a learned actor/critic
  loop, which is part of E3.
