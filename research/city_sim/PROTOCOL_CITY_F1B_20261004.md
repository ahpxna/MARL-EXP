# PROTOCOL — F1-B: a bounded second attempt at the retrained-fleet reference, with the convention-complete provider (04/10/2026 22:36; registered before any F1-B run)

**Why.** F1-A1 (C-85) improved agent fuel (−2.61 % [−3.06, −2.16]) but did not establish agent-TL non-inferiority at +0.5 (upper +0.55). Its provider `CITY_spat_forecast_c` has a demonstrated 1 s early error in one yellow branch (C-84). The user's review (`M3_M4_FINAL_AND_F1B_REVIEW_20261004.md`) asks for ONE bounded round, B0 → B1 → one DEV B2 → one decision.
- F1-A1 is kept as the old-version result and is never pooled with F1-B.
- **It is NOT assumed that fixing 1 s rescues the gate.** The fleet may have adapted to the bias; the timing fix may help fuel and hurt time (D-dir, C-72).
- **Scope of a pass:** a useful deployment option (retraining under the new light with a correct provider). It is not a new method. A method claim would also need same-rights retrain / fine-tune baselines and an ablation.

## B0. Provider `CITY_spat_forecast_c2` (new; the old provider, tables, checkpoints and reports are unchanged)

**Definition.**
- `make_spat_c2(table, q)`: the OLD-format table (the same duration samples, no refit) is augmented with the program's non-green durations from NetInfoK, then served by `CITY_spat_forecast_k`.
- That provider is convention-corrected in every branch, including C-84.
- On grid4 (two greens) it must differ from `_c` ONLY in the yellow → green-after-next branch, by exactly +1 s.

**Checks (exit 1):**

| Check | Content |
|---|---|
| KB0-1 | Convention with TRUE switch times on all grid4 RL-H traces available (m2b k0–3, f1a1 t4–t8, M3 prep k0–1): 0 error in every branch (ttr, green → next, green → after-next, non-green → next, non-green → after-next). This is "0 convention error", not "accurate forecast". |
| KB0-2 | Negative controls fail in the RIGHT branch: (i) dropping the first +1 fails green → next (the C-71 branch); (ii) dropping the chain +1 fails non-green → after-next (the C-84 branch). |
| KB0-3 | Old vs new offline on the same states and the same table: identical in every branch except non-green → after-next, where new − old = +1 exactly. Always-green / never-green links are identical; censored trace ends are excluded. |
| KB0-4 | Causality: the forecast at t is unchanged when the trace after t is replaced (shuffled future phases). |
| KB0-5 | No-SPaT rows are unchanged (the evaluator's `none` arm is the old code path). The zero-residual trainer under c2 with 0 episodes ≡ RULE0 under c2 (bit-identical, one seed). All dependency hashes are recorded. |

## B1. Diagnostic DEV (before any retraining): the direct effect of the input fix on FROZEN fleets

- **Traffic:** a NEW declared DEV, grid4 550–564 (15 seeds), generated after a non-existence check. 530–549 is not read for any F1-B choice.
- **Lights:** t4–t8, with their F1-A1 closed-loop tables (`f1a1_20261004/prep`).
- **Fleets:** the four FROZEN F1-A1 checkpoints (F1s_s213_t4 … F1s_s513_t7), crossed over the 5 lights, each with the OLD provider (`fcc`) and with the NEW one (`fc2`), same q 0.1. R and RULE0 use the same configuration.
- **Reported:**
  - paired new − old (fuel, agent / human / city TL; crossed bootstrap over light × fleet × traffic);
  - each version vs R;
  - the number of fleet SPaT calls whose input changed (c2 ≠ c), and its share.
- **B1 is a diagnostic, never a gate.** It measures the input fix, not the benefit of relearning.

## B2. One DEV round of retraining with the new provider throughout the pipeline

**Pipeline (the recipe is unchanged otherwise):**
- **Closed-loop prep regenerated** with c2. The dev fleet L11_s13 drives on the open-loop table at q 0.5 through c2 instead of the uncorrected provider; there are 8 TRAIN episodes per light and the `CITY_m3_train_E.prep` fit is unchanged. Only the fleet's SPaT function is swapped; the light is greedy RL-H, and the λ = 0 tickets do not act.
- **Then:** F1-scratch (`CITY_fleet_train_f1b.py` = `CITY_fleet_train_f1.py` with the provider swapped): zero init, 200 episodes, TRAIN 0–7, q 0.1, the same reward and architecture.
- **Seeds and lights:** 213 / 313 / 413 / 513 under t4 / t5 / t6 / t7, i.e. PAIRED with the F1-A1 runs by seed, light and budget.
- **Checkpoint rule:** the final checkpoint (episode 200); no selection.

**DEV evaluation (550–564; crossed 5 lights × 4 fleets × 15 traffic):**
- F1-B vs R;
- RULE0 under c2 vs R;
- F1-B vs RULE0;
- F1-B (new pipeline) vs F1-A1 fleets under the old provider (paired by seed, light and traffic; from B1).

Because both the tables and the provider logic change, this comparison is "new pipeline vs old pipeline", not "C-84 alone". The C-84-alone effect is B1.

**DEV gate (= F1 §3, unchanged margins):**
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports ≤ R + 0.1;
- unfinished ≤ R.

**The decision is ONE of:**
- **PASS** → freeze and register B3 separately;
- **FAIL** → F1-B stops. No second DEV round, no new variant in this attempt.

## B3 (only after a B2 PASS; registered separately before it runs)

- Independent lights not used for any choice: new RL-H seeds t9…, trained with the frozen q7b recipe. Fleets are trained and evaluated on disjoint light sets where feasible.
- New fleet seeds and new traffic.
- **The size is fixed BEFORE running,** from the F1-A1 variance components (light, fleet, traffic) for the agent-TL margin. There is no sequential extension and no running until the CI clears.
- **Multiplicity:** this is the SECOND confirmatory attempt for the retrained-fleet reference. B3 uses a one-sided α = 0.025 (Bonferroni over A1 and B3); the user may override this before B3.
- Old and new versions are never pooled.

## Predictions

| # | Prediction |
|---|---|
| P-B1-1 | The share of fleet SPaT calls with a changed input is small (< 15 %; the C-84 branch occurs only during yellows). The paired new − old fuel and TL effects on the frozen A1 fleets are inside ±0.5 % / ±0.3 s. Prior: moderate. A fleet adapted to the old bias could also get worse. |
| P-B2-1 | F1-B fuel vs R < 0 (as A1). Agent TL vs A1: unknown sign. **P(DEV gate PASS) is LOW to moderate**: A1's upper was +0.55, and a fix that only affects yellows is not expected to move agent TL by 0.05 s for sure. |

* 22:41 — **B0 results:**
  - **KB0-1 PASS** (108 grid4 traces, 12.6 M observations, 0 error in all branches).
  - **KB0-2 PASS** (no first +1 fails green → next only, −1.0 on 4 951 452; no chain +1 fails non-green → after-next, −1.0 on 1 302 740).
  - **KB0-4 PASS** (2 235 forecasts unchanged when the future is shuffled).
  - **KB0-3 PASS online** (live RL-H:t4 episode: 819 984 identical old / new outputs outside the branch; 101 616 in the C-84 branch, all exactly +1 s).
  - KB0-5 runs at the start of the chain.
  - Smoke: about 10 % of fleet SPaT calls have a changed input.
* **Frozen at launch:** CITY_spat_forecast_c2.py a4091303e92c770a; CITY_spat_forecast_k.py 7848a3f3219b83dc; CITY_f1b_b0_check.py 1f8bb809e1ce3f21; CITY_f1b_probe.py 26e514d4754b5948; CITY_fleet_train_f1b.py 7fa25868582bcde4; CITY_eval_f1b.py f3a9a2dcbb77af65; CITY_f1b_prep.py afd881f72719f77d; CITY_f1b_report.py 015d99e993b060bf; RUN_chain.sh a4b77173f4520b2b; CITY_f1a1_run.py a517bb07ea0e2da3; CITY_m3_train_E.py 48458e5d0e14cc9b; CITY_fleet_v11.py 5205f39256e1c0f4; 

* 22:58 — **Clarifications (user review M3_FAILURE_CAUSES_AND_METHOD_PATH_20261004):**
  - B1 isolates the C-84 logic change because it holds BOTH the checkpoints and the forecast tables fixed (as registered). B2 compares pipelines.
  - **Multiplicity:** B3 at one-sided α 0.025 is a stricter level for the new test. It does NOT make the chain A1 (0.05) + B3 (0.025) a family-wise 0.05 procedure; the simple Bonferroni bound over the two is 0.075. Both attempts are always reported; "one of two passed" is never presented as a single 0.05 test.
