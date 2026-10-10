# PROTOCOL — M3′: receiver-triggered precision commitment (RPC) (04/10/2026 20:36; DRAFT, registered before any M3′ code or run)

Follows M3-E (stopped after DEV, C-68 / C-69), D-dir (C-72: the frozen fleet needs ttg within ±1 s), A2 (C-75) and the M3 DEV comparators:
- fixed-W commitment gives the fleet a benefit (fleet contribution −1.5…−5.1 %) at a large light cost (city TL +5…+24);
- B-ETA DELAYS the switch the requesting car waits for, which costs both.

The two-tier gate (C-69) applies.

## 1. Mechanism (light-side; no fleet or light weights updated; RL-H:k frozen)

**Base controller.** The light is RL-H:k, deciding keep / switch every DT_L = 5 s after MIN_G, unchanged.

**Trigger** (at a decision tick t, light j in green g, no commitment pending at j):
- **receiver** (the candidate): at least one fleet vehicle is ELIGIBLE at j, i.e. approaching on a link served by the other green g′ (red now), the R10 rule is active (distance ≤ 200 m, lane continues), and the receiver sensitivity of the A1 B5 probe is > 0.
- **eta** (ablation): at least one fleet vehicle approaches j on ANY movement with ETA = d / max(v, 1) in [5, 25] s.
- **random** (matched-rate ablation): trigger with probability p_j, set to the receiver trigger rate measured on the common TRAIN trace of RL-H:k with the dev fleet, per light. The seed is fixed per run.

**Commitment time.**
- T_c = t + clip(h_D, H_MIN, H_MAX), where h_D is the policy-aware prediction D: the first future tick at which RL-H:k's own Q-network, with queues held, prefers switch; if none within 60 s, H_MAX.
- H_MIN = 5 s and H_MAX = 20 s (fixed here).
- From t to T_c the light HOLDS g and switches exactly at T_c (yellow onset at T_c). Its own decisions are ignored during the window. After T_c it runs freely again.

**Messages.**
- While a commitment is pending at j: `commitment`, with green end T_c − t for links served by g and green onset T_c + YELLOW + OBS − t for links served by g′ (the S5-verified convention).
- Otherwise: `unavailable`, so the fleet falls back to σ\*. No forecast is published.

**Information rights.** Fleet V2I telemetry (positions, speeds, membership). The receiver trigger also uses the deployed fleet's frozen policy (for the sensitivity check), declared as in M3 A1 B4.

## 2. Arms

| Arm | Definition |
|---|---|
| R | RL-H:k + `unavailable` (fleet = σ\*) |
| RPC-receiver | the candidate |
| RPC-eta, RPC-random | ablations; same commitment rule, different trigger |
| W-c (W ∈ {5, 10}) and B-ETA (W_B = 10) | the M3 comparators, same code as C-68 |
| F1 | the adapted fleet (other rights, reference only), if its DEV gate passes |

## 3. Endpoints

The M3 endpoints apply: M3-1 agent fuel vs R; M3-2 locked limits (city, agent and human TL upper < +0.5; teleports mean ≤ R + 0.1; unfinished ≤ R); M3-4 clean light cost with the A2 shadow fleet; M3-5 message quality (violations must be 0; commitment count and rate per light-hour; lead time distribution).

**Gate:**
- **Tier 1** ("the method helps"): RPC-receiver passes M3-1 superiority with all M3-2 constraints, AND agent fuel superiority vs the best comparator selected on DEV among W-c and B-ETA.
- **Tier 2** ("receiver triggering helps"): RPC-receiver vs RPC-eta and vs RPC-random, agent fuel superiority.

A failure of tier 2 with a pass of tier 1 means the commitment mechanism helps, not the receiver trigger.

## 4. Stages

- **Self-checks (exit 1):**
  - P1: no trigger possible (no fleet) ≡ RL-H:k bit-identical.
  - P2: violations = 0 over a full episode, and every promised green-end and green-onset matches the observed event (both events checked, unlike S5).
  - P3: the random trigger rate matches the receiver trigger rate within 10 % on the common trace.
  - P4: during a commitment the light's own decisions are logged but not applied; outside, actions equal RL-H.
- **DEV:** light seeds 0 and 1, dev fleets s13 and s113, SELECT 100–104 + 200–209, as in M3.
  - There are no tunable knobs (H_MIN and H_MAX are fixed), so DEV only decides the tier-1 gate for confirmation.
  - The best comparator is re-taken from M3 DEV (W-c W 5 and B-ETA 10, both infeasible there).
- **Confirmation** (if DEV tier 1 passes): FRESH 510–529, the 5 new lights t4…t8 × the 4 confirmation fleets, crossed. Providers are not needed, since no forecast is published.

## 5. Predictions

| # | Prediction |
|---|---|
| P-M3′-1 | Violations 0, and the fleet contribution under RPC is negative (benefit), as under exact commitments in C-68. |
| P-M3′-2 | RPC-receiver's light cost (M3-4clean, city TL) is smaller than W-c W 5's (+5.1), because commitments are fewer and use the policy's own predicted switch rather than a fixed delay. |
| P-M3′-3 | Tier 1 on DEV: prior LOW-to-moderate. With a 50 % fleet share, eligible receivers are frequent, so commitments may be frequent and the cost may still exceed the gain. |
| P-M3′-4 | Tier 2: receiver > eta (eta triggers on green approaches too, at cost without benefit). receiver vs random: unknown. |

## 6. Honest scope

Commitment with a horizon under adaptive control is close to SAE J2735 minEndTime semantics and to priority-request systems (MMITSS). The candidate's specific content is the TRIGGER (only when a deployed frozen receiver is actually consuming the timing) and the TIMING (the controller's own predicted switch, not a delay). Novelty is to be assessed only if tier 1 and tier 2 pass.

* 20:38 — **Checks:** **P1 PASS** (RPC with no trigger ≡ RL-H:0, bit-identical, traffic 0). **P2 PASS** (1 121 commitments, 0 green-end and 0 green-onset violations, traffic 0).
* **Traffic-0 smoke (not an endpoint):** RPC-receiver vs RL-H: agent fuel +10.3 %, agent TL +9.2, city TL +5.4. This is disclosed before the screen.
* **P3:** rates were measured on the common TRAIN trace (RL-H:k + dev fleet s13, measure mode, TRAIN 0–7): eligible-tick rate 0.248 (k0) / 0.242 (k1), per light 0.23–0.27 (`m3p_20261004/rate/rates.json`). The random-vs-receiver commitment-rate match is checked from the DEV sidecars.
* **Frozen before DEV:** CITY_m3p_rpc.py 89ed42e7b2b269d9; CITY_eval_m3p.py a877207461de65f9; CITY_eval_m3p_shadow.py 0b406dee5d0bd54a; RUN_m3p_dev.py 0e2bb3b2650f060c; CITY_m3p_dev_report.py 20a6fed6a5a54d8a;
