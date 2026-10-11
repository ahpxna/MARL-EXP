# PROTOCOL — N2: does a state-conditioned, movement-specific time-to-green forecast help the frozen fleet more than the age-only one? (05/10/2026 00:18; registered before any N2 run)

**Hypothesis** (user list N2). The forecast lacks state (queues, recent history) and targets the wrong quantity (a sum of per-phase quantiles instead of the time to the link's green).

**Data.**
- grid4 RL-H:k (k 0, 1) with the frozen dev fleet (k0 → L11_s13, k1 → L11_s113), the fleet using provider c2 at q 0.1 (the deployed condition). TRAIN 0–7.
- Logged every second: phase, spent, halting / vehicles on each green's lanes, and the fleet's SPaT queries per light (`CITY_n2_collect.py`).

**Model** (`CITY_n2_fit.py`).
- **Target:** the observed seconds to the end of the current green (ttr) or to the target green's next onset (ttg), in the trace convention verified by the convention checks. Censored rows are dropped.
- **Features:** phase position, spent, target flag, halting / vehicles on the current and target greens' lanes, mean of the last two completed run lengths of both greens, light one-hot.
- **Architecture:** MLP 64-64 with two monotone quantiles (0.1, 0.5), pinball loss, rows weighted by 0.25 + fleet queries.
- **Splits:** train seeds 0–5, validation 6–7, early stopping. Separate models per k.

**Comparator on the same data.** The age-only table fitted on the same train files, served as provider c2.

**Offline:** validation MAE / bias / ±1 s / early share, uniform and query-weighted.

**Online provider** (`CITY_spat_forecast_n2.py`, `CITY_eval_n2.py`).
- Features are computed live. The run-length Tracker counts a run ending at the query second as completed, as the offline builder does.
- **KN2-1 / KN2-2:** online feature rows ≡ offline rows, and predictions ≡ the model on the offline rows. Smoke at 00:2x: 9 859 rows, 0 mismatches.

**Endpoint panel.** DEV 600–611, crossed k × fleet (s13, s113).
- Arms: R and c2 q 0.1 (the N1 rows), c2 q 0.5, state q 0.1, state q 0.5.

**Decision (registered).**
- FORECAST BETTER iff the query-weighted MAE is ≥ 10 % below age-only at both q for both k.
- **N2 SUPPORTED** iff, at some q, state − c2 (same q) has an agent-fuel upper bound < 0 with agent TL upper < +0.5 (paired). That is 2 looks, reported.
- **If the forecast is better but the endpoint is not:** stop optimising forecast error (the user's rule).
- Every arm vs R is reported. An arm meeting every M3 limit vs R becomes a candidate for N4 / confirmation.

**Prediction.**
- Forecast better: likely on grid4 (queues inform switches of a queue-driven DQN).
- Endpoint gain: uncertain. D-dir (C-72) says early errors cost fuel and late errors cost time.
- Prior for SUPPORTED: moderate-low.
