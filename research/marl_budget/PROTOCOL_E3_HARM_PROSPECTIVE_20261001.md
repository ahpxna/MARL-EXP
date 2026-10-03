# Pre-specified PROSPECTIVE test of the exploratory "relay harm at low capacity" finding

Written 01/10/2026 11:4x EDT, BEFORE any run on the panel below.  Source of the hypothesis: the EXPLORATORY probe
PROTOCOL_E3_PROTOCOL_CONDITIONED_DEMAND_20261001 (read 11:3x), which was written after protocol 1's result.  The predictors
below were computed on the DEVELOPMENT panel (seed901–904 × 8/16) and are fixed here; the target panel is new.

## Panel
Traffic seeds 3001–3064 × headways 8 and 16 s (128 episodes), used once; checked unused at 11:38 by parsing every
manifest's traffic seeds.

## Arms
relay6Cage_st_s0 … s9 under age-first, const K ∈ {1, 2, 3}, relay v6 evaluator (identical to protocol 1's arms) vs
distill_none_s0 … s9 (no messages).  Endpoint gain_s(K) = −(Σ waiting relay / Σ waiting Z − 1) × 100, 128 paired episodes.

## Predictors (fixed; e3_protocol_demand_report_20261001.json, development panel)
net_S = S_protoS − harm_S (protocol-conditioned, student-level net satisfied demand); S_best = oracle best-subset demand;
harm_S = share of receiver-steps where the local observation alone was acceptable and the student's action on the
delivered relay view is not.

| s | net_S(1) | net_S(2) | net_S(3) | S_best(1) | S_best(2) | S_best(3) | harm_S(1) |
|---|---|---|---|---|---|---|---|
| 0 | 0.0705 | 0.1870 | 0.2142 | 0.1811 | 0.2292 | 0.2650 | 0.0844 |
| 1 | 0.1768 | 0.2601 | 0.2975 | 0.1635 | 0.2548 | 0.3093 | 0.0604 |
| 2 | 0.0689 | 0.2366 | 0.2762 | 0.1709 | 0.2393 | 0.2826 | 0.1100 |
| 3 | 0.0454 | 0.1405 | 0.1661 | 0.1533 | 0.1939 | 0.2179 | 0.0785 |
| 4 | 0.1287 | 0.1939 | 0.2276 | 0.1699 | 0.2366 | 0.2794 | 0.0673 |
| 5 | 0.0860 | 0.1795 | 0.1955 | 0.1704 | 0.2260 | 0.2628 | 0.0828 |
| 6 | −0.0374 | 0.1004 | 0.1159 | 0.1197 | 0.1960 | 0.2067 | 0.1362 |
| 7 | 0.2302 | 0.3072 | 0.3269 | 0.2158 | 0.2682 | 0.3355 | 0.0614 |
| 8 | 0.0080 | 0.0187 | 0.0363 | 0.0582 | 0.0673 | 0.0748 | 0.0524 |
| 9 | 0.1437 | 0.1640 | 0.1704 | 0.1998 | 0.2233 | 0.2158 | 0.0390 |

## Rules (fixed now; unit = seed, n = 10)
- H1: Spearman(net_S(1), gain(1)) ≥ 0.5 AND > Spearman(S_best(1), gain(1)).
- H2 (replication of the K = 1 loss): mean over seeds of gain(1) < 0 with the two-level bootstrap (seeds, then traffic
  seeds within each; 4000 draws; generator seed 0) upper bound of the mean RELAY EFFECT above 0, i.e. relay worse than Z.
- H3: mean over K ∈ {1, 2, 3} of Spearman(net_S(K), gain(K)) ≥ 0.5.
- Comparators reported for every rule: N_s (V-D10), teacher margin (v4), S_best.
- If H1 and H3 fail, "protocol-conditioned harm" is dropped as an explanation (a development-panel coincidence).

Launcher `scripts/RUN_marl_e3_harm_prospective.sh`, report `scripts/MARL_e3_harm_prospective_report.py`, both written
before the runs.
