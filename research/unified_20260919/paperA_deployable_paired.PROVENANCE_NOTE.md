# `paperA_deployable_paired.json` — the locked P-2 panel, paired over rules

Recorded 2026-09-25. Resolves deviation P-2 (the pilot `paperA_deployable.json` had 24 runs per
cell at `M = 1` only).

| item | value |
|---|---|
| producer | `scripts/EXP_paperA_deployable_paired.py`, sha256 `42e94d6338beb8f1…` (recorded as `source_sha256`) |
| rules | imported unchanged from `scripts/EXP_paperA_deployable.py`, sha256 `1197faecbf9cdaeb…`; the same hash as the pilot artifact's `source_sha256` |
| locked configuration | sha256 `a321f1074e3f121b…` (`locked_config_sha256`): `r ∈ {1,2,4}`, `M ∈ {1,4}`, base and swapped worlds, rules `surrogate_at_estimate`, `geometry`, `uniform`, `alpha = 0.05`, budget `B = 60000`, 200 runs per cell, check every 50 rounds |
| seeds | `np.random.default_rng([20260926, r, int(M), int(swapped), run_index])`, shared by the three rules of a cell (common random numbers) |
| artifact | `research/unified_20260919/paperA_deployable_paired.json`, sha256 `5d4a41dbea0264c0…` |
| checkpoint | `research/unified_20260919/paperA_deployable_paired.partial.jsonl` (one line per finished cell; kept) |
| interpreter | `.venv/bin/python` |
| wall time | 7695 s (launch 3) |
| self-checks | 5/5 (certificate sides, accounting, pairing, per-rule binomial alpha test over launched runs, transcribed `oCount_le_bad`, min slack 0.29) |
| figure | `research/papers/_figures/paperA_deployable_paired.pdf`, sha256 `3c94d3c7098c6e7b…`, from `scripts/FIG_paperA_deployable_paired.py` (sha256 `66bb77e11de740c2…`, 7/7); record `paperA_deployable_paired_figure.json` (sha256 `e2fff1f53c16a79a…`) with the paired table |

## Launch history

- Launch 1 (source sha `70202bb3843ee8a5`) finished every run and crashed in the alpha self-check
  (float overflow in a binomial tail, and the check conditioned on stopping). No artifact.
- Launch 2 (source sha `1a37ef8d51c1b35b`, archived at `legacy/EXP_paperA_deployable_paired_launch2_1a37ef8d51c1b35b.py`)
  finished 31 of 36 cells and was killed with its terminal session (launched without `nohup`).
  It wrote no per-run data; its log `work/run_logs/paired_launch2.log` (sha256 `737b1f507d0e…`) keeps
  the 31 cell summaries.
- Launch 3 (this artifact) added a per-cell checkpoint that resumes only under the same locked
  configuration and rules hash, and ran under `nohup`. It resumed nothing (`resumed_cells = 0`).
  **Reproduction:** every one of launch 2's 31 cell summaries (restricted mean, stopped, wrong,
  censored) is reproduced exactly; the figure script checks this (`--launch2-log`).

## What the rules are, and what they see

As in the pilot (`paperA_deployable.PROVENANCE_NOTE.md`): three tracking learners with warm start,
forcing `min(1, 1/√t)` and the first argmax of `W − N`, whose oracles see only the running
estimate. No rule reads `theta`; the true world enters only through the simulated observations.
Each run stops when the certificate of the answer its estimate retains clears the threshold and
returns that answer.

## What was measured

- 7200 launched runs; 6258 stopped; **none stopped with a wrong answer**. Per rule over launched
  runs: 0/2400 each. All 942 censored runs are `surrogate_at_estimate` runs on the base world.
- Base world (answer A): the surrogate rule certifies 167, 41, 44, 2, 4, 0 of 200 runs at
  `(r, M) = (1,1), (1,4), (2,1), (2,4), (4,1), (4,4)`; geometry and uniform certify every run.
  Paired excess of `min(tau, B)` over geometry: 19056, 46921, 48598, 54015, 53904, 46318 rounds,
  bootstrap 95% intervals excluding 0 in every cell; the surrogate rule is slower in 86.5% to
  100% of pairs. Median middle share: surrogate 0.050, geometry 0.467, uniform 0.500.
- Swapped world (answer B): every rule certifies every run, and the surrogate rule is FASTER than
  both others in every cell (paired difference against geometry between −163 and −1249 rounds,
  intervals excluding 0). There the surrogate's frozen cells are the informative ones.

## Scope

- `min(tau, B)` is a restricted mean: a censored run contributes `B`. Where the surrogate rule is
  censored, its mean and its paired excess are LOWER bounds on the uncensored quantities.
- The certificate is a valid lower bound on the retained answer's likelihood ratio, not the
  exact infimum of `tauG`, and `alpha = 0.05` lies far above the `delta_0` of
  `surrogate_learner_cost`. The panel is evidence about these rules on this family, including the
  direction and size of the base/swapped asymmetry. It is not a test of the `Ω(log²(1/δ))` order.
- The bootstrap intervals are numerical (10000 resamples, fixed seed), over the 200 independent
  pairs of a cell.
