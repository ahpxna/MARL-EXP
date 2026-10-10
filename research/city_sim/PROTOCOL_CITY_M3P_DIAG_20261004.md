# PROTOCOL — M3′-D: a 2 × 2 diagnostic of two RPC design choices (H1 forced hold, H2 message withdrawn at yellow) (04/10/2026 22:58; registered before any run)

**Declared post hoc.** It is designed after seeing M3′ DEV (C-79) and M3-NC (C-86), following the user's audit (`M3_FAILURE_CAUSES_AND_METHOD_PATH_20261004.md` §4, §7 H1 / H2, §8.1). It is a CAUSAL diagnostic, not a method screen. No result here is a method claim. A good cell could only motivate a newly registered candidate with its own confirmation.

## Factors (everything else = registered RPC-receiver: RL-H:k frozen, trigger, h_D, H_MIN 5 / H_MAX 20, receiver probe)

**F (forced hold):**
- F1 = registered: when the trigger fires, the light holds at least 5 s even if RL-H chose switch now.
- F0 = no forced delay of the CURRENT decision: if RL-H chose switch at the trigger tick, the light switches now and a zero-hold commitment T_c = t is recorded (its yellow → green schedule is known); otherwise the registered T_c = t + clip(h_D, 5, 20).

**M (message lifetime):**
- M1 = registered: commitment while pending, `unavailable` from T_c.
- M0 = keep: after T_c, links served by the committed next green g′ keep receiving ttg = (T_c + YELLOW + OBS) − t until that onset; all other links get `unavailable`.

Cell (F1, M1) is the registered RPC. It is re-run with the new code and must equal the registered C-79 rows bit-identically (check KD-1).

## Panel (the M3′ DEV panel, unchanged)

- Light seeds k 0 / 1, dev fleets L11_s13 / s113 (frozen), traffic SELECT 100–104 + 200–209 (15).
- R = the M3 DEV R rows.
- Shadow per cell (`SHADOW:` fleet) for the common-denominator decomposition.
- Crossed bootstrap over [k 2, fleet 2, traffic 15].

## Measurements

| What | Content |
|---|---|
| Endpoints | Per cell, M3-1 agent fuel % vs R; city / agent / human TL. Mechanism cost x = 100 (S − R) / R; fleet contribution y = 100 (A − S) / R. |
| Factor effects | Main effect of F (F0 − F1, averaged over M), main effect of M, and interaction. Paired cells, crossed bootstrap. |
| **H1 log** (new) | At every trigger: RL-H's chosen action and Q-gap (Q_switch − Q_keep). At every held tick: the action RL-H would choose and its Q-gap. Reported: the share of commitments issued against a switch decision; the share of held ticks where RL-H would switch; the mean positive Q-gap. |
| **H2 open-loop step** | Record the (F1, M1) light phases and commitment lists. Replay the SAME light schedule with M1 messages (must reproduce the closed-loop rows: replay-fidelity check KD-3) and with M0 messages. This isolates the message change with the light fixed. The closed-loop (F1, M0) cell then shows it with the light reacting. |

## Checks (exit 1)

- **KD-1:** (F1, M1) under the new code ≡ the registered RPC-receiver rows (all 15 seeds, k0 / s13 and k1 / s113 at least).
- **KD-2:** 0 green-end and 0 onset violations in every cell, including F0's zero-hold commitments and M0's kept messages, whose promised onset is the one checked.
- **KD-3:** replay with M1 messages ≡ the closed-loop (F1, M1) rows. If not bit-identical, the H2 open-loop step is reported as approximate, with the difference.
- **KD-4:** no-trigger (`none`) ≡ RL-H:k (inherited P1).

## Predictions (priors)

| # | Prediction |
|---|---|
| P-D1 (H1) | F0 lowers the mechanism cost x relative to F1. The share of commitments issued against a switch decision is ≥ 30 %. Prior: moderate. |
| P-D2 (H2) | M0 makes the fleet contribution y more negative than M1, open-loop and closed-loop. Prior: moderate. The fleet may already be at the stop line when the message disappears. |
| P-D3 | No cell beats R on agent fuel within the TL limits. Prior: high; WC5 and RPC lost by large margins. |

**Stop rule.** One run. If no cell shows net benefit, H3 (the continuation opportunity check) decides whether any commitment-selection learner is worth building. No new RPC variants are opened from this diagnostic.

* 23:01 — **Smoke, disclosed before the panel** (seed 100, k0 / s13, 600 s, not endpoints):
  - KD-1: (F1, M1) ≡ the registered RPC, bit-identical.
  - KD-3: the replay with M1 messages ≡ closed loop, bit-identical.
  - 57 % of commitments are issued against a switch decision (95 / 166).
  - Agent fuel by cell: C11 78 028, C01 73 430, C10 75 897, C00 71 380.
  - Open-loop keep − withdraw: −2.3 % agent fuel, +0.95 s agent TL.
  - 0 violations in every cell.
* **Frozen at launch:** CITY_m3p_rpc2.py d2496d830443e1b8; CITY_eval_m3p2.py 0c296e750aa35b00; CITY_eval_m3p2_replay.py 55c388f7be6bbab8; CITY_m3p_diag_report.py 2ad2a965d276a5b0; RUN.sh 1a6e398921919b6c; CITY_m3p_rpc.py 89ed42e7b2b269d9; CITY_eval_m3p.py a877207461de65f9; CITY_eval_m3.py 6ee43e55d635247b; CITY_eval_m3_shadow.py 65f5274431386abd; 
* 23:54 — C-92 runner bug: 24 / 32 cells did not run. Rerun queued as `005_M3pD_fix.sh` (RUN_fix.sh sha cb20b5e4e3af8d55 (bash-3.2 fix: no wait -n)); design unchanged.
