# E3 results audit — every evaluation since 29/09 18:00 (01/10/2026, 09:2x–09:58 EDT)

User 08:5x: "đọc lại hết đống kết quả mà m chạy hqua"; 09:5x: "m tự tổng hợp eval đi" (no agents: an 8-agent workflow
launched at 09:13 died on the session limit with nothing returned).  Done by hand, read-only, per AGENTS.md.

## What was inspected
- CENSUS `scripts/MARL_e3_results_census.py` → `research/marl_budget/e3_results_census_20261001.{json,md}`: 1033 arms
  (actor × rule) from every COMPLETE evaluation directory since 29/09 18:00, each paired with the zero-byte student of the
  SAME training seed on the SAME episodes (958 paired; 75 unpaired by design).  1206 manifests: all COMPLETE (778 with
  self_check PASS, the rest are trainings / older evaluators without the field).  0 checkpoints newer than their evaluation.
- Ledger rows L-97 … L-202, the eight pre-registered protocols, the report scripts of each family, the order / relay /
  adapter code where a result looked suspicious.

## Checks that PASSED (with the evidence)
| Check | Evidence |
|---|---|
| The zero-byte comparator does not depend on the capacity process | `models/marl_comm_actor.py` CommAdapter.encode has no capacity / budget field (own sensors, phase, time, message blocks only); distill_none config `adapter: default`; empirically `set_full_s0` rule `none` gives +3.79 % [+2.82, +4.74] under capacity `high` AND `iid` (byte-identical rows).  So Z(iid) is a valid comparator for cap4 / low cells, including the reserved panel. |
| No training / selection seed touches any evaluation panel | the scenario caches of all 121 training runs in `e3_delivery_actors_20260929` contain exactly 72 seeds: 301–364 (train) and 401–408 (select); none of 901–964, 2001–2064, 2101–2164, 2201–2264, 2301–2364, 2401–2464, 2501–2564, 2601–2664, 2701–2764. |
| Direction-A comparator D_s matches its source | D_s = 1 − last `agree` in `distill_none_s<s>.log`: 0.081 0.076 0.069 0.061 0.080 0.125 0.102 0.043 0.031 0.069 — 10/10 equal to PROTOCOL_E3_COMM_VALUE_PREDICTOR. |
| Decision-depth probes do not perturb the closed loop | probe rollouts vs the original evaluations: 18/18 byte-identical (cage s0–s9 agefirst/low vs satrot relay6Cage; relay_st s0/s1 × {agefirst, prefix} × {iid, low}). |
| Eight pre-registered verdicts follow their rules | FRESHONLY (vs set_none: pass both; vs the zero-byte student it LOSES +1.26 / +2.11 %, stated in L-144), BYTEBUDGET (−2.94 / −3.69 %, supported), FOSTUDENT (s0 −0.76 [−1.65, +0.12] ⇒ not supported), SETFRESH (s1 +7.2 % ⇒ not supported), TRAINEDQ4 (−5.35 / −4.23 %, supported), ROBUST_OOD (−3.84 / −2.16 %, supported), RELAY_ROTATION (6/6 cells, supported), TEN_SEEDS (supported, L-201).  Census CIs equal the ledger's to ±0.02 (bootstrap draws). |
| Ledger numbers of the relay / rich7 / theory families | L-182 (rich7), L-184 (1)(2)(4), L-187 (B12), L-177 (V-A, V-S values), L-197 (relay6_st age-first mean −1.70, relay6Cage −1.78, all-win 6/10 and 5/10) recomputed from rows: equal. |
| Three byte-identical coincidences are explained, not bugs | hub ≡ bass under rich7 (last step's rich receiver always holds the freshest table: nested prefixes, L-181); deadline2 ≡ deadline3 at low capacity (the D2 promoted list contains D3's, both oldest-first, and the senders with worst age ≥ 3 always exceed the largest K, so the decoded prefixes coincide; promoted counts differ 25415 vs 18859); `*_full` ≡ `*_bc3_fo` (3 B packets let every sender through, 5850 B = full: the byte channel removes the capacity constraint, L-162). |

## Findings (none is a bug in a reported result)
| # | Kind | Where | What | Correction |
|---|---|---|---|---|
| F1 | REPORTING (my census) | `scripts/MARL_e3_results_census.py` first run | rows without an `actor` field (decision-depth probes) were all paired with Z_s0 | fixed (seed from the directory name; unknown ⇒ unpaired) and re-run; also: directories whose rows hold several hand-coded controllers without an actor field (`e3_mp2_message_check*`, `ref_maxq`) are grouped incorrectly in the census and must be read from L-114 / L-116 instead |
| F2 | CLAIM OUTDATED | paper_marl_v2.tex l. 490–494 and 655–656; L-184 (3) | "a decision-sensitivity codebook (B8) beats both bars in all twelve cells, under both orders" / "also repairs relay under the congestion order" — true for seeds 0–1, but the overnight seeds lose SIGNIFICANTLY under the congestion order: s3 low +1.57 [+0.82, +2.41], s4 cap4 +0.91 [+0.05, +1.74], low +2.34 [+1.44, +3.23], s5 cap4 +1.23 [+0.30, +2.22], low +1.07 [+0.21, +1.93] | the codebook's order-robustness holds on 2 of 5 seeds (B8) and 1 of 2 (B12); rewrite both passages |
| F3 | WORDING | L-177 | "relay + agefirst MONOTONE on s1" means "no adjacent K → K+1 step raises waiting significantly" (the report's definition); waiting rises gradually K3 → K5 (1138 → 1147), which that test cannot catch | state the definition wherever "monotone" is used |
| F4 | BORDERLINE | L-197 | "one losing cell (s9 iid +0.76 [+0.01, +1.58])" — lower bound at the boundary (≤ 0 with the census draws); "relay6Cage congestion losing cells on 5 seeds" — 4 seeds (s0, s3, s6, s8) significant in the census, s5 / s9 at the boundary | call these boundary cells, not losses / wins |
| F5 | INCOMPLETE | `e3_grid4x4_20260930` | only seed-0 actors exist; phase 2 (relay evaluation) died with ENOSPC at 01:46 (`phase2_s0.log`); seeds 1–3 have no actors | the 4×4 claim stays "planned" in the paper (it is, l. 673–675); rerun now that 55 GB are free |
| F6 | MISSING ARMS | overnight queue | relay6B8 s2 / s6–s9, relay6Clow s2–s9 never ran (disk); relay6B8_st_s4 has no age-first row | "training at the target capacity also repairs relay" rests on 2 seeds |
| F7 | PROVENANCE GAP | every manifest | checkpoints are referenced by path, never by hash | mtimes show no checkpoint changed after its evaluation; add a sha256 of the checkpoint to future manifests |

## What the evidence supports for the main claim
- Relay + age-first beats the distilled zero-byte student under heterogeneous prefix capacity: development (10 seeds,
  all-win 5–6/10, no significant losing cell), relay-rotation panel (6/6 cells), reserved ten-seed panel (iid −2.29 %,
  cap4 −2.04 %, low −1.26 %, all upper < 0; vs the replicate students too).
- The ORDER is the operative lever at short prefixes: the congestion order loses the advantage at cap4 / low on the
  reserved panel (+0.15 %, +0.38 %) and on most development seeds, as the freshness theory predicts; at constant K = 1
  even age-first only ties the zero-byte student (V-S: s0 +0.83 %, s1 −0.86 %).
- Effect sizes are 1–3 % of waiting; three of ten pairs (s5, s6, s8 on the reserved panel) are individually null.

## What it does not support
- Order-robustness of the decision-sensitivity codebooks (F2).  Any 4×4 or second-network claim (F5).  Generality beyond
  one simulator, one 3×3 network, one channel model.
