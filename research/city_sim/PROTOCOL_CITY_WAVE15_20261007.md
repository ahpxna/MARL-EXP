# PROTOCOL W15: making the method stronger, more robust and more general (registered 07/10/2026, 13:2x, before any W15 run)

User request (07/10, 13:1x): run items 1–4 and everything in the improvement table:
- zero-shot default;
- uncertainty-aware rule and state-dependent quantile;
- projected-queue adapter;
- policy-aware forecaster;
- quantile revision under IDM;
- online calibration.

Shared infrastructure:
- Statistics, limits and self-checks are those of W13/W14: crossed bootstrap B = 2000; M3 limits; KM13-1a/1b; modes wrapper.
- Fresh traffic is generated only after a non-existence check.
- No existing script is edited. New code is `scripts/CITY_w15_*.py`.

Traffic allocation (grid4 unless stated):

| Item | Traffic |
|---|---|
| W15-1 confirmation | 1040–1059 |
| W15-2 | 1060–1079 |
| W15-3a (IDM) | 1080–1099 |
| W15-4 grid4 | 1180–1199 |
| W15-4 spider | spider 1210–1229 |
| W15-4 rand3 | rand3 740–759 |
| W15-5 online days | 1200–1239; evaluation 1240–1259 |
| W15-6 | 1260–1279 |

## W15-1 Zero-shot default (job 091)

Offline evidence, from W13/W14 tuning data only (selection data, 15 grid4 lights): one setting (A, B, q) = (1, 0.25, 0.1) on every light gave
- mean fuel −4.81% (HBEFA4) and −2.98% (PHEMlight5);
- worst light −2.26% (PHEMlight5);
- every light with agent TL ≤ 0.

Per-light R13-RB gave −4.94 / −3.18. **The default is fixed now: TG = (1, 0.25, 0.1).**

**FRESH3 panel.** A new, independently trained set of five lights and four fleets:
- lights RL-H t19–t23, DQN seeds 11 + 100t, 120 episodes;
- fleets R10 s1413, s1513, s1613, s1713, 400 episodes;
- four F1-B fleets, 200 episodes from scratch, fleet seed s(1413 + 100i) under light t(19 + i).

**Calibration.** The FRESH2 recipe for the forecaster only: traces, open-loop table, closed-loop c2, N2 logs, fit, KF-2. The adapter and q are not tuned for TG. For comparison, the full R13-RB tuning (TRB) is also run.

**Arms** (t19–t23 × s1413–s1713 × 20 on traffic 1040–1059, under HBEFA4 and PHEMlight5): R, TG, TRB, F1B.

**Decisions:**
- **D15-1** (α = 0.05): TG meets every M3 limit and saves fuel (upper < 0) under both emission models.
- **D15-1b** (α = 0.05): TG − F1B fuel (HBEFA4) upper < +0.5 pp.
- **Descriptive:** TG − TRB, which measures the value of per-light tuning.

## W15-2 Uncertainty-aware rule and state-dependent quantile (job 093; FRESH2 panel)

**(a) Rule R15-U.** As R13-RB, but the agent-time constraint uses an upper bound over the four TUNE seeds:
- mean + 1.645 · sd / √4 of the per-seed agent-TL differences must be ≤ 0;
- city and human mean differences must be ≤ 0;
- then argmin of max(fuel_H4, fuel_P5);
- if no configuration qualifies, choose the minimum agent-TL upper.

**(b) State-dependent quantile.** `CITY_w15_qstate.py` replaces the provider's fixed q by
- τ = 0.1 + 0.4 · σ(a − b · w/10 − c · h/30);
- w is the forecast interval width q0.5 − q0.1 of the answer, h its horizon (ttg or ttr), both in seconds;
- the published value is the linear interpolation p0.1 + (τ − 0.1)/0.4 · (p0.5 − p0.1);
- the yellow (c2 table) branch stays at q 0.1.

Grid and selection:
- a ∈ {−2, 0, 2}, b ∈ {0, 1, 3}, c ∈ {0, 1, 3}: 27 configurations at the default adapter (1, 0.25).
- TUNE 660–663 with fleet L11_s13, under HBEFA4 and PHEMlight5.
- R15-U selects per light among these and the W13 grid (A, B, q) rows.

**Arms** (t14–t18 × s1013–s1313 × 20 on traffic 1060–1079, both models): R, TRB (the W13 choice), TU (the R15-U choice), TG (default), F1B.

**Decisions:**
- **D15-2a** (α = 0.05): TU meets every limit and saves fuel under both models.
- **D15-2b** (α = 0.05): TU − TRB agent TL upper < 0 and TU − TRB fuel upper < +0.5 pp under both models. In words: less agent time without material fuel loss.

## W15-3 IDM

**(a) Quantile revision under IDM (job 092).**
- Use the W13-6a IDM-recalibrated tables and networks.
- Tuning grid C × q ∈ {0.1, 0.5} under IDM (HBEFA4 and PHEMlight5), TUNE 660–663. The q 0.5 HBEFA4 rows are reused from w13/idm/tune.
- Selection: R13-RB.
- **Arms** (traffic 1080–1099, every vehicle IDM): R, TOLD (the W13-6a choice, q 0.5), TRB, TF, F1B.
- **D15-3a** (α = 0.05): TRB meets every limit and saves fuel under both models.

**(b) Online calibration under model shift (job 096; descriptive).**
- Setting: the Krauss-calibrated FRESH2 providers are deployed in an IDM world.
- Arms (network-wide configurations): OFF (R) and 5 settings, {(1,0.25,0.1), (1,0.5,0.1), (1.5,0,0.1), (1,0.25,0.5), (1,0.5,0.5)}.
- Days are fresh seeds 1200–1239. Fleet s1013 runs on all five lights, one configuration per day.
- **Algorithm:** safe successive elimination.
  - Round-robin over the active arms, OFF included.
  - After each round, an arm is eliminated if its mean agent TL exceeds OFF's by more than +0.5 s/veh (one-sided 90% Welch bound), or if its fuel is not below OFF's (mean ratio ≥ 1).
  - Stop when one non-OFF arm remains or the 40 days are used. The output is the remaining arm with the lowest mean fuel, or OFF.
- **Evaluation:** fresh IDM traffic 1240–1259, all fleets, chosen arm − R. Reported descriptively, together with the days used.

## W15-4 Projected-queue adapter (job 094)

**Definition.** Light input h_g is replaced by h_g + #{moving vehicles on g's served lanes with ETA ≤ τ}, where ETA = (lane length − position)/max(speed, 0.1). The parameter is τ ∈ {3, 5, 10, 15} s. Vehicle counts n_g are unchanged.

**Networks:**
- **grid4 FRESH2:** grid τ × q ∈ {0.1, 0.5} × both models on TUNE; rule R13-RB; traffic 1180–1199.
  - Arms: R, TRB (W13), TP (projected-queue choice).
  - **D15-4a** (α = 0.05): TP meets every limit and saves fuel under both models.
- **One-lane spider:** grid τ × q on TUNE 1100–1103; traffic spider 1210–1229.
  - Arms: R, TRB (W14-3 choice), TP.
  - **D15-4b:** sixth attempt of the spider chain, α = 0.0015625. TP meets every limit and saves fuel under both models. Chain bound 0.0984.
- **rand3:** grid τ × q; traffic rand3 740–759.
  - Arms: R, TOLD (W10-6 choice), TP.
  - **D15-4c** (α = 0.05; first test of the revision on rand3): TP meets every limit and saves under both models.

The implementation is registered by amendment before launch.

## W15-6 Policy-aware forecaster (job 095)

**Definition.** The provider knows the deployed light's frozen DQN and its input adapter. At each second it projects, for each served lane group:
- the queue: halting vehicles plus vehicles whose ETA (current speed, floored at 2 m/s) has passed while red;
- arrivals: approaching vehicles at their ETAs;
- discharge: on green, 2 s per vehicle per lane.

It then rolls the DQN forward through its decision epochs (Δ = 5 s, minimum green, 3-s yellow) on the projected observations, adapter applied, up to 90 s. It answers time-to-green and time-to-red from the projected schedule. Yellow answers stay exact. No log is used for training.

**Tuning.** Arms PRF (projection only) and PRF+q01 (the projection's answer, but never later than the network's q0.1), at the default adapter, on TUNE. Rule R13-RB over {PRF, PRF+q01, TG}.

**Arms** (FRESH2, traffic 1260–1279, both models): R, TG, TPRF (the chosen PRF variant).

**Decisions:**
- **D15-6** (α = 0.05): TPRF meets every limit and saves under both models.
- **Descriptive:** TPRF − TG, and the served-answer error published versus shadow.

The implementation is registered by amendment before launch.

## Order

091 (W15-1) → 092 (W15-3a) → 093 (W15-2) → 094 (W15-4) → 095 (W15-6) → 096 (W15-3b).
- Jobs are added as their code passes a smoke test.
- A failed self-check stops its job.
- A failed decision is reported as "not shown" and does not reopen its rule.

## Amendment A1 (13:2x, 07/10): implementation of W15-1/2/3a/4, registered before any W15 result

**W15-1.**
- `CITY_w15_run.py` maps RL-H 19–23 to the FRESH3 lights. The rand3 runner maps 21–25 separately; the two are never loaded together.
- `CITY_w15_prep.py` copies the W8 prep with the light range changed.
- The TG adapter is applied as `--light-obs q:1:0.25` with `--n4 0.1:hyb:…`.
- The smoke passed end to end, with 1-episode trainings.

**W15-2.** `CITY_w15_qstate.py` wraps the network class `CITY_n2_fit.QNet`. Its q0.1 column becomes p(τ), and the provider runs at q 0.1.
- KQS-1 PASS: with τ → 0.1 (a = −100), the row equals the W13 q 0.1 row T_t14_a1_b0p25_q01, seed 660, bit for bit, including the action digest.
- KQS-2: (0, 1, 1) differs.

**W15-3a.** The IDM runs go through `CITY_w13_idm.py` (W13_EM for PHEMlight5). Selection and report use `CITY_w14_gen.py`; its D14-1 is D15-3a.

**W15-4.** `CITY_w15_pq.py` patches `CITY_env.LightRL.obs` (two-green) and `CITY_lightk.LightRLK.obs` (multi-green). The stock adapters are switched off (q:0:0, RLKQ:ckpt:0:0). The reference R never uses the adapter.
- KPQ-1 PASS: τ = 0 reproduces the raw light bit for bit (grid4 t14, seed 660, 600 s).
- At τ = 10 the mean green falls from 17.1 to 12.6 s in that smoke.
- Spider runs chain `CITY_w15_pq` → `CITY_w14_q` (for q); rand3 runs chain `CITY_n3_run` → `CITY_w15_pq`.
- Selection (`CITY_w15_pq_eval.py select`) is R13-RB over τ × q, with ties broken by the smaller τ and then q 0.5.

All four smokes passed. Queue order: 091 (running), 092, 093, 094.

## Amendment A2 (13:3x, 07/10): W15-6 implementation (`CITY_w15_prf.py`), registered before any W15-6 TUNE or confirmation run

**Development on one tuning episode** (t14, seed 660, the default adapter; descriptive, not used for any decision). The first version, which projected only the vehicles already on the lanes, predicted the next switch about 11 s late: on queried green seconds, MAE 17.2 s and bias +10.9 s. A per-group arrival-rate estimate was therefore added:
- new vehicle ids per second on the group's lanes, averaged over at least 30 s;
- entries reach the stop line after a free-flow traversal of the mean lane length.

With the arrival estimate, the same episode gave a projected-switch MAE of 8.2 s (bias −0.8). On the same queried seconds, the wrapped network's time-to-red gave 10.6 s (bias −6.8) at q 0.5 and 15.1 s (bias −14.9) at q 0.1.

**The design is frozen as follows:**
- arrival model on; horizon 120 s;
- decision epochs every 5 s, with minimum green 5 s;
- time-to-red is T + 1 and time-to-green is T + 3 + 1, where T is the projected switch;
- the wrapped N4 hybrid provider runs at q 0.1 and supplies the yellow, all-green, gating and no-switch fallback answers;
- variants: prf, and prfq = min(prf, the wrapped answer).

**Selection:** R13-RB over {prf, prfq, tg}. If tg is chosen for a light, TPRF on that light is TG.

**Accounting:** the sidecars record the projected and network switch-time errors on queried green seconds. These are descriptive.

The smoke passed end to end. Job 095 is queued after 094.

## Amendment A3 (13:3x, 07/10): W15-3b implementation (`CITY_w15_online.py`), registered before any W15-3b run

**Day outcomes.** Because the simulator is deterministic, every arm is run on every day (1200–1239; fleet s1013; lights t14–t18; IDM through `CITY_w13_idm`). The elimination loop reads only the rows of the arm it plays on that day, so the result equals an online run. A day's outcome is the mean over the five light checkpoints of agent fuel and agent TL.

**Elimination rule**, applied after each round to every non-OFF arm with at least 2 days:
- the arm is eliminated if the one-sided 90% Welch lower bound of (agent TL − OFF agent TL) exceeds +0.5 s/veh;
- or if its mean agent fuel is not below OFF's.

**Stopping and choice.** The run stops at one remaining non-OFF arm, or after 40 days. The choice is the remaining non-OFF arm with the lowest mean fuel; if none remains, OFF.

**Evaluation.** Every arm is evaluated on fresh IDM traffic 1240–1259, with all fleets and both emission models. This is descriptive; it shows whether the online choice is the best arm in hindsight.

The smoke passed. Job 096 is queued last.
