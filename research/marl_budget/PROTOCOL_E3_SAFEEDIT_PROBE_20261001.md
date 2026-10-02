# Pre-specified EXPLORATORY probe: a SafeEdit gate between the relay student and compiled silence (A-H5)

Written 01/10/2026 20:5x EDT (`date` 20:49:58 before writing), BEFORE any run of the probe below.  User 20:4x: "chạy probe
safeEdit đi".  Source of the hypothesis: subagent A (a5e043f5fc399c33b, AGENTS_ROSTER_20261001.md), H5 — `LeanMarlSafeEditV1.safe_rule_never_harms`,
`threshold_sharp` and a staleness-indexed error ε(b) = e0 + ν·b give the gate "use the relay action iff its margin exceeds
2ε(b)", with a predicted crossover b* = (γ/2 − e0)/ν to be compared with the hand-tuned b3 > 6 gate.

## Why (state before this probe)
- The tuned gate (PROTOCOL_E3_GATE_PROSPECTIVE_20261001, b3 > 6 → Z) repairs +0.78 % at K = 1 on its prospective panel but
  falls back on 72 % of decisions and stays −0.59 % [−1.17, +0.02] below Z (GT1 not supported).
- A margin-aware rule falls back only where the relay's preference is small relative to its staleness-indexed error.
- Facts that limit the reading (checked 20:3x): the students are trained by cross-entropy on the teacher's argmax
  (`MARL_e3_actor_distill_v7.py`), so their logits are not values; the teacher is an actor-critic with a STATE-value critic,
  so no per-action value exists anywhere.  The only per-action score is the teacher's logit, which defines A_0.25.  Hence
  "harm" below means "the teacher scores the chosen action below Z's action" — a DECISION-level diagnostic, not return.

## Probe (scripts/MARL_e3_safeedit_probe.py, written before the runs)
- Closed loop: relay6Cage_st_s<s> acting on its actual merged view (age-first, relay v2 merge, 3 B codebook), capacity iid
  (K = 0) and const K = 1; development episodes 901–904 × 8/16; seeds 0–9.  The closed loop is that of
  MARL_e3_age_cf_probe.py / MARL_e3_negflip_probe.py: queue sums must equal e3_negflip_20261001/s<s>_K<K>/rows.json (parity,
  self-check that can fail).
- DIAGNOSTIC ORACLE per receiver-step (not deployable, recording only): the teacher's logits T on the full fresh
  counterfactual view (`pre_flags`), Z's action a_Z from the empty view (re-derived; its acceptability flag must equal
  `pre_flags`' flag, self-check).
- Relay logits ℓ on the actual view and on 11 synthetic views in which every relayed inbox entry (age > 0) is relabelled to a
  common age a = 0..10 decision steps, content unchanged (the re-ageing of MARL_e3_age_response_probe.py).  Recorded: b3 of the
  actual view (Σ (age − 3)+ over inbox entries, the gate's statistic), number of relayed and fresh entries, never-heard count.

## Analysis (scripts/MARL_e3_safeedit_report.py, written before the runs)
- Link (logit → teacher scale), per student seed s, fitted on iid ACTUAL views only: centred over valid actions,
  c_s = Σ x·y / Σ x² with x = ℓ − mean ℓ, y = T − mean T.  Required c_s > 0.
- f = T − mean T, f̂ = c_s (ℓ − mean ℓ), a_R = argmax ℓ; per-decision per-value error ε_i = max(|f̂ − f| at a_R, at a_Z);
  estimated gain ĝ = f̂(a_R) − f̂(a_Z) ≥ 0; true gain g = f(a_R) − f(a_Z).
- Calibration pool: iid states, variants "actual" and a = 1..10 (a = 0 is impossible for a relayed copy and is excluded), all
  seeds pooled; b = b3 of the (synthetic) view.  Bins of b: {0}, (0, 3), [3, 6), [6, 9), [9, 12), [12, 18), [18, ∞); bins with
  ≥ 200 decisions.  ε_q(bin) = 90 % quantile of ε_i (a DIAGNOSTIC quantile, not a certified bound).  OLS fit
  ε_q = e0 + ν·b over the bins at their median b.  γ = median ĝ over iid actual-view decisions with a_R ≠ a_Z.
- Gates evaluated on K = 1 ACTUAL views (states of the ungated relay's own loop, d^R — the known caveat: not the gate's own
  trajectory): SE (relay iff ĝ > 2(e0 + ν·b3), else Z), G6 (Z iff b3 > 6), R (relay always), Z.
- Endpoints per seed then mean: acceptability acc = P(T(chosen) ≥ max T − 0.25); net vs Z = acc − acc(Z); harm vs Z =
  P(f(chosen) < f(a_Z)); fallback share; coverage = P(ε_i ≤ e0 + ν·b3) (the Lean hypothesis at both actions).
- Theorem self-check (transcribed `safe_edit`): among K = 1 and iid decisions where coverage holds and SE edits (a_R ≠ a_Z,
  ĝ > 2ε(b)), g > 0 for EVERY one.  A failure is an implementation bug; the report refuses to print.

## Predictions and kill criteria
- P1 drift (kill A-H5 if not): ν > 0 and Spearman(bin median b, ε_q) ≥ 0.8.
- P2 threshold: b* = (γ/2 − e0)/ν ∈ [3, 12] (a factor 2 around the tuned 6).  Outside → the principled threshold does not
  reproduce the tuned gate (b* < 0: SE almost never edits — the v1 outcome).
- P3 transfer (descriptive, no kill): coverage on K = 1 states vs in-sample iid coverage.  K = 1 coverage < 0.85 → real
  stale content adds error that synthetic re-ageing (age label only) cannot see.
- P4 decision level at K = 1: SE net vs Z > R net vs Z (mean over seeds, and in ≥ 6/10 seeds), and SE harm < R harm.
  Fail → SE is not a better repair than no gate even at the decision level; no closed-loop test follows.
- Descriptive: SE vs G6 (net vs Z, harm, fallback).  If P1, P2 and P4 hold, a closed-loop prospective test on an unused
  panel is written as a separate protocol before any run.

## WITHDRAWN before the full run (01/10/2026 20:5x EDT, `date` 20:54:13; L-229)
Only a one-episode smoke ran (scratchpad se_smoke1, K = 1 and iid, s0, seed 901 load 8: parity PASS, 234 records each); no
analysis was computed and no record of it enters any report.  Reasons (user audit 20:5x, verified):
1. The only available instantiation takes f = teacher logit (no per-action value exists: students are trained by
   cross-entropy on the teacher's argmax, MARL_e3_actor_distill_v6.py l.123/137; the teacher's critic is a state value).
   SafeEdit would then certify "the teacher scores the relay action above Z's", a decision-level statement on d^R — the very
   proxy that H6 showed does not track return (4×4 K = 1: same-state +0.010, own trajectory −0.042).
2. The "margin > 2(e0 + ν·b)" form of A-H5 is the argmax-stability certificate of `LeanMarlDecisionLifetimeV1.
   relay_action_equals_fresh` / `LeanMarlDecisionCertificateV1.lifetime_from_drift_rate` (relay action = fresh action),
   not SafeEdit (value improvement); the hypothesis conflated them.  This protocol's SE rule is a correct SafeEdit
   instantiation only with f = teacher logit, hence point 1.
3. ε(b) would be a fitted quantile, not a certified bound (the v1 lesson); and the hold-r prospective result (L-228) shows
   b = B_3 does not order cells across K (K = 3 r = 6, B_3 5.95: +0.33 %; K = 2 r = 3, B_3 5.31: −0.23 %).
4. Novelty of a fallback gate is low: SPIBB / Soft-SPIBB, Simplex runtime assurance, ADMAC (AAAI 2024, per-message
   reliability), DACOM (AAAI 2023, delay-aware), CAIC.
The open problem that would make it worthwhile — a channel-derived CERTIFIED bound on a continuation-value error — has no
object to build on in this pipeline.
