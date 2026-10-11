# PROTOCOL SPIDER-TSI: the two-sided interface on a second network (registered 05/10 ~07:05, before any spider TSI code was run)

**Question:** does the TSI method (C-118, grid4) transfer to an independent network, with its procedure unchanged (fleet-side hybrid state forecast; light-side demand adapter; per-light calibration from training traffic only)?

## Setting (M4 assets, unchanged)

- **Network:** spider (`research/city_sim/net/spider.net.xml`): 18 signals, 12 with two greens, 6 with three greens.
- **Lights:** the learned multi-green controllers RLK_sp11 / RLK_sp111 (`CITY_lightk.LightRLK`, frozen).
- **Fleet:** the frozen rule GLOSA-L∘σ\* (the spider M1 learned fleet was not confirmed, C-80; the rule is the frozen receiver).
- **R:** RLK + no SPaT (the rule then drives as σ\*).

## Procedure (the grid4 method, generalized to K ∈ {2, 3} greens; no quantity of the confirmation traffic enters it)

1. **Collection:** TRAIN 0–7 per light, the fleet using the M4 forecast-K provider at q0.1 (`s3b/prov/fkcl_rlk<k>.json`); per-second feature log.
2. **Forecaster N2K** (`scripts/CITY_n2k_fit.py`): N2's MLP quantile model; train seeds 0–5, validation 6–7.
   - Features are relative to the cycle: event kind; yellow flag; the number of greens to pass before the target (one-hot 0 / 1 / 2); spent; K = 3 flag; halting and vehicles on the greens at relative positions 0 / 1 / 2; the mean of the last two runs of those greens; light one-hot.
   - Targets: end of the current green run, or the next onset of each other green. Censored rows dropped.
3. **Fleet-side service (direct-only hybrid, per C-113):**
   - during a yellow whose next green serves the link → the forecast-K answer (exact there);
   - otherwise N2K at q0.5;
   - links served by consecutive greens → forecast-K.
4. **Light-side adapter** `RLKQ:A:B`: the RLK inputs "halting on the current / next green's lanes" become halting + A·count(0.1 ≤ v < 2) + B·count(2 ≤ v < 5). RLK weights are frozen.
5. **Per-light calibration** on NEW TUNE seeds 1100–1103 (non-existence check):
   - grid (A, B) ∈ {(0, 0), (1, 0), (2, 0), (1, 0.25), (1.5, 0.25), (1, 0.5), (2, 0.5)};
   - rule as in TSI-2: agent TL point ≤ −0.25 and city / human ≤ 0 vs R → the most fuel; else the minimum agent TL.

## Checks

- **KS-1:** offline / online feature and prediction parity of N2K on a TRAIN smoke run (as KN2-1 / KN2-2).
- **KS-2:** the hybrid and adapter counters are > 0 in the smoke run.

## Confirmation (one attempt)

- **Panel:** fresh spider traffic 1110–1129 (20 seeds, non-existence check) × lights RLK11 / RLK111 × the rule fleet.
- **Arms:** R, TSIK, HYBK (service only), ADPK (adapter only).
- **Bootstrap:** crossed over light (2) and traffic (20). With only two light seeds this is a conditional claim on these two lights.

**Decision (α = 0.05 one-sided):** SECOND-SETTING REPLICATION PASS iff TSIK vs R meets every M3 limit:
- agent fuel upper < 0;
- city / agent / human TL upper < +0.5;
- teleports ≤ R + 0.1.

Reported as-is either way. Components are described as on grid4.

## Amendment A1 (07:2x, before tuning or confirmation)

**KS-2 FAILED in the first run (job 041):** the provider's N2K path never answered (n2k = 0 of 7 947 valid queries).
- Cause, mine: a tuple-unpacking error in `make_provider` (the cache holds six elements; five were unpacked).
- The rule fleet's `CITY_glosa_lane` swallows exceptions without counting, so the error was silent apart from KS-2.
- KS-1 parity had passed: 0 mismatches on 9 844 rows.

**Fix:**
- The unpacking is corrected.
- The provider now counts its own exceptions, and KS-2 requires exc = 0 as well as n2k > 0 and fk_direct > 0.

The stale KS1 smoke files are moved to `check/legacy_ks1_v1/`. The collection data and the models are unaffected (deterministic refit). Requeued as `042_SPIDER_TSI.sh`; nothing else changed.

## Amendment A2 (07:3x): SPIDER-TSI-2, the second and LAST spider attempt (registered BEFORE the first spider confirmation result was read; only the TUNE table had been seen)

**What the TUNE table showed:**
- No configuration qualified.
- The service alone (0, 0) is catastrophic on spider: fuel +22.7 / +17.9 %, agent TL +64 / +55 s/veh.
- Agent time falls monotonically as B rises: +1.36 / +0.95 at B = 0.5, the grid's edge. The registered grid was too narrow for spider's stronger hidden-demand effect.

**Change (only the grid):**
- (A, B) ∈ {(1, 0.75), (2, 0.75), (1, 1.0), (2, 1.0), (1, 0.5), (2, 0.5)} on the same TUNE seeds 1100–1103.
- The same selection rule.

**Confirmation:**
- fresh spider traffic 1130–1149 (non-existence check);
- the same lights and fleet;
- arms R / TSIK2 / HYBK / ADPK2.

**Decision:** α = 0.025 one-sided (second attempt; Bonferroni bound 0.075 with the first). The first attempt's verdict stands as-is.

Job `043_SPIDER_TSI2.sh`.
