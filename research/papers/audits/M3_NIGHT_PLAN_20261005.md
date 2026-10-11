# M3 night plan 04→05/10 (written 23:55; the user: "lập kế hoạch trước", then execute from the next wake)

**Standing order** (user, verbatim summary): every wake keeps the old duties.
- Plus the MANDATORY hypothesis list (`METHOD_HYPOTHESES_NIGHT_20261004.md` N1–N8, the six-row table in the user message, and the RPC / H3 items).
- Sub-hypotheses and failure diagnostics are allowed; new hypotheses from interesting patterns are allowed.
- Mind machine capacity, but everything is finished tonight.
- **At the 04:51 wake:** if no M3 success and EVERY hypothesis has been fully tested → full re-read (results, ledgers, reports, code, branches; known failure causes; what a method paper still needs; the ledger from C-1; failures as method sources; deep comparison with recent work). The deliverable is a hypothesis list, each with the novelty to prove, the competitor to beat, and a small decisive test.
- At that point, **"fetch" is authorized:** the two roster subagents (a5e043f5fc399c33b, acae5606e7dd259e7 — reuse via SendMessage; recreate with the same role only if they cannot be resumed). The three of us work TOGETHER and argue; the work is not split.

## 0. Rules for every hypothesis

- A short protocol (with the decision rule) before any run.
- Smoke inside the queued job; ledger row; no gate moved.
- "Tested" = the registered decisive test ran AND its verdict is written (support / reject / inconclusive with the reason). A failure gets one cheap diagnostic of WHY, when the data allow it.
- **Capacity:**
  - All new runs go through `research/queue_night_20261005` (one job at a time; ≤ 4 simulation processes per job).
  - Nothing runs beside the queue except the already-launched F1-B chain.
  - Load, swap and disk are checked at each wake (disk guard 15 GB).
- **Seeds:**
  - Fitting / selection: grid4 TRAIN 0–7.
  - New N-series DEV: **600–611** (fresh; generated in the first N job after a non-existence check).
  - Confirmation reserve: **700–739** (untouched until a candidate is frozen).
  - Old panels 450–564 are never reused for a new choice.
- **Primary setting:** grid4, learned light RL-H (k 0 / 1 for development), frozen learned fleet R10 (L11_s13 / s113). R = RL-H + no SPaT (fleet → σ\*). Endpoint: agent fuel vs R with the city / agent / human TL limits.
- Spider (rule fleet) is a secondary check only where cheap.

## 1. Hypothesis registry (status at 23:55)

| ID | Hypothesis | Decisive test (registered before run) | Depends on | Job / status |
|---|---|---|---|---|
| D1 (H1) | The RPC forced hold (≥ 5 s against a switch decision) is a cost source | M3′-D 2 × 2, factor F | — | **005** queued (C-92 rerun) |
| D2 (H2) | Withdrawing the message at yellow onset loses fleet benefit | M3′-D factor M, plus the open-loop replay (light fixed) | — | **005** |
| H3 | A commitment-selection opportunity exists (closed-loop continuation) | 96 situations × 7 options, full-episode outcomes | — | **010** queued |
| N1 | Part of the harm comes from forecasting beyond the tail support | (a) Exposure: the share of FLEET queries answered by the fallback, plus errors and harm by support state. (b) Arm "c2-tail": only the fallback is replaced by `unavailable`, everything else is c2. DEV 600–611 × k0 / k1 × s13 / s113, vs c2-all and R. Spider secondary (rule, RLK, DEV 100–109). | — | **020** to build |
| N2 | The forecast lacks state / has the wrong target | Direct movement-specific TTG forecaster (queue / halting / arrivals on the serving and conflicting approaches, phase, age, recent green history); a regularized gradient-boosted quantile model on TRAIN logs (split by episode; censored targets handled). Target = the observed time to the link's green (joint, not a sum of quantiles). Compared with age-only c2 on the SAME data: query MAE / bias / ±1 s at the fleet's own queries, and the endpoint on DEV (same arms as N1). | logger | **030** to build |
| N3 | Publishing the forecast changes its target (feedback) | (a) Paired branches from the same prefix: at t\* ∈ {1200, 1800, 2400} the fleet starts USING the forecast in branch A and keeps ignoring it in branch B. The forecast is computed in both; both lights are closed-loop. Measured: switch-time shifts, queues, forecast error after t\*, endpoint. (b) Calibration under the deployed service policy (refit on data logged while the fleet uses it) vs one-shot open-loop fit, with the SAME amount of data. | N2 forecaster | **040** |
| N4 | Selective provision helps: some contexts benefit from SPaT even though always-on does not | Service gate (forecast vs `unavailable`) from causal features (forecast interval width, the frozen receiver's command variation across the plausible TTG range, the queue / externality state). Fitted on TRAIN paired rollouts with a small grid / CEM. Screened on DEV vs publish-all, confidence-only, ETA, and random at the matched activation rate. Full episode. | N1 / N2 provider | **050** |
| N5 | Utility ≠ sensitivity | On the H3 data: selection rules (sensitivity-only, cost-only = Q-gap, receiver+cost, a learned utility regressor) fitted on H3 seeds 0–1 and applied to held-out seeds 2–3. The REALIZED gain of the chosen options, out of sample (the branch outcomes exist, so this is offline). | H3 | offline after 010 |
| N6 | Cheap timing: commit when the base policy switches anyway | H3 options P (follow RL-H) / Z (force now) / H-holds, split by RL-H's action at t\*; RPC-D F0 vs F1; out-of-sample rule as in N5 | H3, D1 | offline after 005 / 010 |
| N7 | One-edit gains do not add up | The best candidate rule (from N4 or N5 / N6) applied at EVERY qualifying tick for a full episode. The realized gain is compared with the sum of the H3 single-intervention gains for the same rule, on DEV. | N4 / N5 | **060** |
| N8 | A learned cycle / split controller (a predictable action space) is a cheaper way to keep the frozen fleet's benefit | Learned per-light splits within a cycle (green durations from a small parameter vector, fitted by CEM on TRAIN with the frozen fleet and EXACT program SPaT). The objective is agent fuel with TL penalties vs R. Compared with RL-H + R and RL-H + best service on DEV. Not a new method: a structural baseline (HONEST-CAV / DHCP-like). | — | **070** |
| F1-B | Reference (retrain with c2) | Registered B2 DEV gate | — | **DONE: FAIL by 0.01 (C-94)** |
| opt H4 | Fine-tune fails because of exploration / value init | Reset std / value head, same budget | — | only if time remains |
| opt H5 | A constrained fleet objective meets the NI margin | Lagrangian on agent TL, same budget vs F1-scratch | — | only if time remains |

**Order** (information value × cost): 005 → 010 (both queued) → 020 (N1, cheap) → 030 (N2 data + fit) → 070 (N8; independent, long) → 040 (N3) → 050 (N4) → 060 (N7). N5 / N6 run offline as soon as 010 / 005 finish. One queue job at a time.

## 2. What counts as M3 success tonight

- A candidate (most likely N4's service gate, or a commitment rule from N5 / N6) beats R on agent fuel within the TL limits on DEV 600–611.
- It also beats the strongest simple comparator chosen by a SELECT rule (publish-all with the best forecaster, confidence-only, ETA, random at the same activation).
- Then: freeze, register the confirmation on 700–739 with new lights / fleets (crossed), run it, and only then claim.
- A DEV win is a candidate, not M3. F1-B (retrain) is a reference with more rights.

## 3. Timeline (approximate; re-planned at each wake)

| Wake | Actions |
|---|---|
| 00:51 | Read F1-B B2 (decision), 005 if done. Build 020 / 030 code and smoke them inside the queue jobs. |
| 01:51 | Read 010 (H3). Run N5 / N6 offline. Queue 070, 040. |
| 02:51 | Read N1 / N2 / N8. Build and queue 050 (N4) with the best provider. |
| 03:51 | Read N3 / N4. Queue 060 (N7) on the best rule. Any candidate → freeze and register the confirmation. |
| 04:51 | All hypotheses have verdicts. Either confirmation runs, or the full re-read with 2 subagents (fetch authorized) to produce the next hypothesis list (novelty, competitor, decisive test). |
| 05:51 → 11:51 | Continue per the outcome (confirmation analysis, or the debate's top decisive tests, through the queue). |

## Status at 00:46 (05/10)

| ID | Verdict | Row |
|---|---|---|
| D1 (H1, forced hold) | SUPPORTED: −4.54 % fuel when removed | C-95 |
| D2 (H2, withdrawal) | SUPPORTED: −2.80 % fuel when kept; open loop −2.66 % | C-95 |
| H3 | Registered YES, but max-of-noise (chaos) | C-96 |
| N1 | REJECTED: tail exposure 0.11 % | C-97 |
| N5 | REJECTED out of sample; noise floor SNR ≈ 0.2 | C-98 |
| N6 | REJECTED (within noise) | C-98 |
| N2 | SUPPORTED vs c2: −3.3 % fuel vs R, but agent TL +2.1…+2.3 → not a candidate | C-99 |
| N2M (sub-hypotheses of N3) | Hidden demand SUPPORTED (adapter −0.8 s); time cost FLEET-INTRINSIC in open loop; the fuel gain comes from the light's reaction | C-100 |
| N7 | SUPPORTED from existing data: single-edit effects do not add; RPC +9.4 % | C-101 |
| N4 | Running (job 033) | — |
| N4 + adapter (GQ) | Queued (032a1) | — |
| X3 (exact on replay) | Queued (032a) | — |
| N8 | KN8-1 caught a SPaT error at smoke → fixed (A1), queued (032b) | — |
| N3 (a) pub vs shadow accuracy, (b) refit under service | Queued (034) | — |

Added from the ChatGPT-audit cross-check (`CHATGPT_AUDITS_CROSSCHECK_20261005.md`): X1 (quantile of the sum), X2 (error by horizon / state), X3, X4, X5 (done in N5), X8–X10.

## Hypothesis coverage diff at 01:39 (user 01:39: every hypothesis tested or written + queued)

| ID | Source | Status | Action |
|---|---|---|---|
| D1, D2, H3, N1–N7 | mandatory | **tested** (C-95…C-109) | — |
| N8 | mandatory | **queued** 036 (KN8-1 fixed twice) | wait |
| TSI | candidate from N2 / N2M / HYB | **confirmation running** (032f); KT-1 queued 033 | wait |
| X1 quantile of sum | audit LIT | null on grid4 (structure); spider-only | **write: N2 on spider** (fit + DEV, rule fleet) → queue |
| X2 / X3 / X5 | audit | done (C-102 / C-107 / C-98) | — |
| X4 receiver-aware gate | audit HYP §3 | conditional on method A being a candidate; N4 family rejected | recorded as not applicable unless A revives |
| H4 reset std / value head | audit FAIL §7 (optional) | untested | **write + queue** (fleet fine-tune, F1 trainer, 4 runs) |
| H5 Lagrangian agent-TL constraint | audit FAIL §7 / FINAL §6 (optional) | untested | **write + queue** (F1 scratch + constraint) |
| X10 H-PATH upgrade order | audit CORPUS §5 | untested | **write + queue** (F1-B fleets under FT; path table) |
| HYB-direct (c2 only when the next green follows the yellow) | C-113 | untested | **write + queue** (SELECT, new registration) |
| LEFT-permissive (green `g` but must yield) | user question 01:3x | untested | **write + queue** (TSI with left links unavailable vs TSI; per-direction diagnostic) |
| X9 paper wording / CIs | audit | text | at the paper pass |
| SPIDER-TSI (2nd network) | user 02:0x: stop, save tokens | **not run**; recorded as an open scope limit (second network untested for TSI) | — |
