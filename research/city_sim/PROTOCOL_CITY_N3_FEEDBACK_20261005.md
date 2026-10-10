# PROTOCOL N3: publication feedback (registered 05/10 ~00:44, before any N3 run; complements N2M's open-loop arm)

**Hypothesis N3** (`METHOD_HYPOTHESES_NIGHT_20261004` §2): publishing the forecast changes its own target. The fleet's response changes queues, and the light reacts. A calibration made under the deployed service may then serve the fleet better than a one-shot fit.

Prior art inside the repo: the closed-loop refit already exists (`CITY_m3_train_E.py:59`). Only the specific component is tested here; no novelty is claimed for "refitting".

## (a) Does publishing degrade accuracy at the fleet's own queries?

Paired runs, same seeds and policies (DEV 600–611; RL-H k0 / k1 × R10 s13 / s113):
- `pub`: the fleet receives N2 q0.5. This equals N2q05 (check KN3-1, endpoint equality on the panel).
- `shadow`: N2 is computed at every fleet query, but the fleet receives `unavailable` (σ\*; traffic as in R).

Every 5th valid query is scored against the realized event (`scripts/CITY_eval_n3.py`; convention identical to the N2 offline builder). Metric: MAE and bias, for ttg (link waiting for green) and ttr (green link), by realized-horizon bucket.

**Decision:** FEEDBACK DEGRADES ACCURACY iff the ttg MAE (pub − shadow), per (k, fleet, seed) with the crossed bootstrap, has lower bound > 0. If the upper bound is < 0, publishing IMPROVES accuracy. Otherwise NOT DETECTED.

## (b) Calibration under the deployed service

- Collection: 16 TRAIN episodes (seeds 0–7 × k), with the fleet USING N2 q0.5 (`pub`, featlog).
- Fit `n3_k<k>` with the unchanged `CITY_n2_fit.py`: same features, architecture, split and epochs. The data count equals the one-shot model's (16 episodes; there the fleet used c2).
- DEV: `refit` (pub with n3_k) vs the one-shot N2q05 rows.

**Decision:** CALIBRATION UNDER SERVICE HELPS iff refit − one-shot (paired, crossed) has agent fuel upper < 0 or agent TL upper < 0, with the other endpoint's point estimate not worse by more than +0.5 (TL, s/veh) / +0.5 % (fuel). Its ttg query MAE is reported.

Each refit / pub arm is also reported vs R under the M3 limits (candidate status).

**Scope:** one forecaster family, one quantile, one refit round. The protocol allowed up to two rounds; one is used for time.
