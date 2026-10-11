# PROTOCOL W14: does the W13 method generalize, and is it robust? (registered 07/10/2026, 02:09, before any W14 run)

Context. W13 (084) showed, on the FRESH2 panel, that choosing per light the adapter (A, B) **and the published quantile q ∈ {0.1, 0.5}** by
rule R13-RB (time limits as points on TUNE, then min of max(fuel_HBEFA4, fuel_PHEMlight5)) gives a fuel saving under both emission models
and fuel non-inferiority (indeed superiority) to the F1-B retrained fleets. One panel is not a method claim. W14 tests the same method,
unchanged, on the two earlier grid4 panels, and its robustness to the W9 channel/sensing perturbations. Rules, code and statistics are those of
W13 (`CITY_w13_modes.py`, crossed bootstrap of `CITY_w6_report_v2`, KM13-1a/1b); new scripts `CITY_w14_gen.py`, `CITY_w14_robust_report.py`.

## W14-1 Generality (job 088)
Panels (lights × frozen fleets; providers and networks as originally calibrated; development fleet L11_s13; TUNE 660–663):
- **TSI2**: RL-H t4–t8 × s213–s513; F1-B arms of the TSI-2 confirmation available. Fresh traffic 980–999.
- **W71**: RL-H t9–t13 × s613–s913 (W7-1 fresh-policy panel). Fresh traffic 1000–1019.
Per panel: tuning grid C × q ∈ {0.1, 0.5} under HBEFA4 and PHEMlight5 (q 0.5 HBEFA4 rows reused from the panel's original tuning);
R13-F and R13-RB exactly as in W13; fresh traffic generated after a non-existence check; arms R, TOLD (the panel's registered TSI, q 0.5),
TRB, TF (and F1B on TSI2), each under both emission models.
- **D14-1** (per panel; α = 0.05 one-sided, first test of the W13 method there): TRB meets every M3 limit vs R and TRB − R agent fuel upper < 0
  under HBEFA4 **and** under PHEMlight5.
- **D14-2** (TSI2 only; α = 0.05): TRB − F1B agent fuel (HBEFA4) upper < +0.5 pp, with TRB meeting every limit.
- The method is called general on grid4 only if D14-1 passes on both panels; otherwise the report states on which panel it failed.

## W14-2 Robustness (job 089; descriptive, as W9)
On the W13 confirmation rows (FRESH2 × 900–919, HBEFA4): TRB and TW8 under 1-s minimum delay (query cache), 20 % and 50 % loss, 80 %
adapter detection, 1 m/s speed noise (CITY_w9_run modes, unchanged). Per perturbation: arm − R (limits met? fuel upper < 0? one-sided 95 %)
and TRB − TW8.

## Later (amendments before launch)
W14-3 the W13 method on rand3 and both spider builds (multi-green provider; the one-lane spider chain is at its fifth attempt, α = 0.003125);
W14-4 a quantile scan (networks refitted with q ∈ {0.05, 0.1, 0.2, 0.3, 0.5}) and a bias scan of the published time, to test the newsvendor
reading τ* = c_late / (c_early + c_late); W14-5 an action-side green cap for the one-lane spider.

Smokes: 088 and 089 passed end to end (02:07–02:09; scratchpad). Spool order: after 086, 087.

## Amendment A1 (02:11, 07/10): W14-3, one-lane spider (job 090); registered before any W14 result

The multi-green evaluator (CITY_m4s_tsi_eval) hard-codes q 0.5. `CITY_w14_q.py` replaces it with W14_Q, in both the N2K network and the
forecast-K table fallback, as the grid4 hybrid uses one q for both branches. In the smoke, a q 0.1 row differs from its q 0.5 twin (agent TL 28.65 vs 29.72) and records w14_q.

Grid and selection:
- Grid: the union of the two registered spider adapter grids (11 settings) × q ∈ {0.1, 0.5} × {HBEFA4, PHEMlight5}, on TUNE 1100–1103.
- Lights RLK 11 / 111, with the rule fleet GLOSAL:0.3 and the attempt-1 N2K networks and tables.
- The q 0.5 HBEFA4 rows are reused from sptsi_20261005/tune and tune2.
- Selection rule: R13-RB.

Confirmation:
- Fresh spider traffic 1190–1209, generated after a non-existence check.
- Arms: R, TOLD (the attempt-1 choice at q 0.5) and TRB, each under both emission models.

Decision:
- **D14-3** is the fifth attempt of the one-lane spider chain, so α = 0.003125 one-sided.
- It requires that TRB meets every M3 limit against R, and that TRB − R fuel has upper < 0 under both emission models.
- The family-wise bound over the five attempts is 0.0969, conditional on each test holding its nominal level.

The smoke passed end to end; its rows are not evidence (one seed, 600 s). Job 090 is queued after 089.
