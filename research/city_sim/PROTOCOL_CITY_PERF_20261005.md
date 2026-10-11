# PROTOCOL PERF: does the light-side adapter reduce the performative sensitivity of the forecast target? (registered 05/10 ~04:56, before the run)

**Motivation:**
- The research pass (performative prediction: Perdomo et al. 2020; Drusvyatskiy & Xiao; consistent anticipatory guidance: Bottom & Ben-Akiva 2000; small-gain theorem) suggests a measurable quantity: how much publishing the forecast shifts its own target.
- N3 (C-109) measured this without the adapter: the ttg MAE rose 1.70 → 3.02 s, and the share of red waits > 30 s rose from 0.089 % to 3.34 %.

**Test:**
- N3's pub / shadow pair, repeated with the light adapter q:2:0 in front of RL-H.
- DEV 600–611, k0 / k1 × s13 / s113, N2 q0.5. Evaluator `CITY_eval_n3.py` + `--light-obs q:2:0`.

**Measures (pub − shadow):**
- ttg MAE;
- the share of scored ttg queries whose realized wait is > 30 s and 15–30 s;
- mean green.
- Each is compared with the same quantities without the adapter (n3_20261005 rows).

**Decision:** SENSITIVITY REDUCED iff the pub − shadow ttg-MAE gap with the adapter is smaller than without it (crossed bootstrap of the difference of differences, upper < 0). Mechanism evidence only.
