# Week review 28/09 → 05/10/2026 (written 00:06 05/10; user: "đọc lại toàn bộ repo, đọc lại toàn bộ results trong vòng 1 tuần qua")

## What was read

- **CITY ledger** C-1 … C-94, in full: rows C-1…C-65 re-read line by line tonight; C-66…C-94 written in this session and re-indexed.
- **MARL ledger** L-142 … L-333 (row index plus the key rows).
- **Claim tables:** E3 legacy-view, two-population.
- **Synthesis notes:** DESTINATION_20261003, WHY_NOT_WIN_REVIEW_20261003, PROPOSAL_SPAT_CONTRACT_20261004.
- **ROADMAP:** headings (Papers A / B / C were closed on 26/09, before this week).
- **Reports:** every report and job log written in the last 150 minutes.
- **Not re-read line by line:** every raw episode, every Lean module, and the earlier MARL rows L-1…L-141.

## Track 1 — E3 / MARL: "Upgrading communication without retraining every agent" (paper draft v2 ready)

**Phenomenon.** Upgrading a channel can break frozen learned receivers even when it adds information. On 4 × 4 the split was −9.35 = +0.22 information − 9.57 excess. Support, not freshness, organises the hazard (train-match, mixture, support diagnostics; L-249…L-294).

**Retraining sits at the reference ceiling.** Matched / MIX receivers are ≈ the full-view teacher, +5–6 % on 4 × 4 (WHY_NOT_WIN §2). So a method can win only on HOW CHEAPLY AND SAFELY it closes the hazard, not on final return. The learned selector and critic failed on ESTIMATION: no within-state ranking, oracle +15.4 per state (September).

**Winning direction: legacy-view emulation.**
- **C1:** a new protocol that keeps the legacy relay structure lets every node rebuild the frozen receivers' K1 view exactly (Lean decoder theorems).
- **C2:** the naive packet breaks it.
- **C3:** the zero-byte emulator is exact iff coverage; coverage failed on 3.8e-5 of steps.
- **C4:** mixed fleet, EMU vs fallback +3.15 [2.24, 4.07].
- **C5:** no detected difference vs FT-mix / PCT retraining.
- **C6:** bytes.
- **Limits:** per-agent NI not established (E13); EMU − ALL-NEW −0.59.

**Open:** an external benchmark (needs download permission), a per-agent NI panel.

## Track 2 — City, two populations (learned lights × learned car fleets)

| Phase | Rows | What it established |
|---|---|---|
| Sensing, support, commitment (02/10) | C-1…C-10 | Eco fleets plus hidden queues harm actuated lights. Per-light compatibility ≠ corridor compatibility. Commitment windows are NOT cheap at the one valid demand level (Q5). Learned-partner upgrade hazard (Q7 / Q7b, 3 / 4 training pairs). Partner-only contracts are not sufficient; in-support semantic harm. |
| Fragile learned fleets (03–04/10 morning) | C-11…C-36 | Determinism fix (PYTHONHASHSEED). The idle loophole (C-13); every Q7 / Q7b fleet is net-harmful vs SUMO drivers (C-17). The reaction repair helps but fleet-off wins (C-14…C-18). B6: no beneficial learned fleet in 4 reward / recipe families. The crawl, the sentinel bug, the residual class excluding SUMO (C-21…C-27). The σ-family dominates 11 / 12 fleets (C-28, C-37). R5h trades fuel for time (C-31). Driver-model upgrades are compatible with learned lights (C-30…C-34). cologne8 light recipe fails (C-35 / 36). |
| SPaT era → **M1 met** | C-37…C-57 | Movement SPaT trace-checked. The reward-B gameability, the eval-release bug (C-41). **Lane-end deadlock under setSpeed** (C-45) → lane-aware release; rule GLOSA-L∘σ\* beneficial (C-46). **R9 (search) −2.80 % vs the rule; R10 (PPO residual) −1.70 %** on fresh traffic (C-54, C-57). |
| M2 | C-58…C-63 | The upgrade FT → RL-H is −33.7 s/veh. Frozen fleets lose their benefit (labelled → exactly σ\*) or are harmed (naive +7 %). The empirical forecast fails (M2b). The oracle replay shows opportunity remains (−6.6 %), but it is NOT a ceiling (C-61 / C-63). |
| M3 light side | C-64…C-79, C-86 | E family (penalised predictability): infeasible on DEV. W-c, B-ETA, predictable cycle, forecast D: infeasible. RPC: tier-1 fail. **M3-NC CONFIRMED the negative for WC5 (+2.98 %) and RPC (+9.26 %).** The mechanism cost exceeds the fleet's closed-loop contribution on grid4. |
| M3 retrain reference | C-78, C-85, C-93, C-94 | F1 fine-tune fails. F1-scratch passes DEV. **A1: fuel −2.61 %, agent-TL NI upper +0.55 (not established).** B1: the C-84 fix alone ≈ 0. **B2: fuel −3.12 %, NI upper +0.51 (FAIL by 0.01)**; the new pipeline is better than the old (−0.50 % fuel, −0.11 TL). |
| M4 spider | C-74…C-83, C-89, C-91 | Learned all-green light −57 s/veh. The rule −9.2 % vs σ\* (TL NI not established on fresh traffic). R9 does not beat the rule. M2 replicates (loss and harm). Commitment W5 +6.7 % with NO fleet contribution. Forecast arm strongly harmful (+14 %, agent TL +30), forecast MAE 22 s with feedback. The adapted fleet under RLK: −1.6 % fuel, +8.7 agent TL. |

## Cross-cutting patterns (what is KNOWN vs NOT known about the failures)

1. **Implementation / interface bugs were the first-order cause of many early "failures",** found by identity checks and traces:
   - the idle loophole (C-13), crawl (C-21), sentinel (C-22), residual cap (C-25), eval release (C-41);
   - the lane-end deadlock (C-45), setProgram handoff (C-18);
   - timing conventions (C-38, C-71, C-84);
   - runner / xargs (C-92), NetInfo two greens (C-83).

   Each fix changed results. A failure is not read as a property of a method until its interface checks pass.

2. **Information value is real but fragile.** M1 shows a −7.6 % class-level SPaT value. M2 / M2b / D-dir show the frozen fleet loses it under timing uncertainty, with asymmetric fuel / time effects.

3. **Light-side certainty is expensive** (WC5 / RPC / E / CYC): the mechanism cost is +5.5…+10.6 % agent fuel on grid4.
   - The RPC H1 log (C11 cells, 60 episodes): **60 % of commitments are issued at a tick where RL-H chose SWITCH; at 56 % of held ticks RL-H would switch**. The forced hold is a direct, measured part of the design's cost.
   - M3′-D will quantify it.

4. **Retraining recovers fuel at a small time cost.**
   - Grid4: about −2.6…−3.1 % fuel, agent TL +0.26…+0.34; non-inferiority missed twice by 0.01–0.05.
   - Spider: −1.6 % fuel with +8.7 TL.
   - The zero-residual rule with the forecast is WORSE than no SPaT (+3.2…+3.7 %), so the learned residual is compensating for forecast error.

5. **Feedback (spider):** the forecast-driven fleet lengthens the learned light's greens. MAE goes 12.8 → 21 s from open- to closed-loop. A hypothesis, not yet isolated (N3).

6. **E3 → City analogy.**
   - E3 won when the new protocol could carry the OLD view exactly (nesting / emulation).
   - In the city, the old fleet's "view" is the light's TIMING itself. Emulating it requires constraining the light (commitment), which is what costs.
   - The analogue of E3's zero-byte emulator would be a service that gives the old fleet an input that keeps its DECISIONS right without forcing the light. This is the N4 / receiver-value direction; untested.

## What a method paper (city) still needs, even if a candidate passes tonight

1. A candidate that beats R and the strongest same-rights comparator (best forecaster publish-all, confidence-only gate, ETA, random) on DEV, then confirmation on 700–739 with new lights and fleets.
2. Novelty vs FoRL, HONEST-CAV, DHCP, probabilistic commitments (S04), integrity gating (S06), performative risk control (S07).
3. A structural baseline with a natural predictable action space (learned cycle, N8).
4. A second network with a LEARNED fleet that passes M1 there. On spider the learned R9 did not beat the rule.
5. An ablation isolating the new component (receiver signal, feedback calibration).

## State at 00:06

- Queue: 005 M3′-D rerun running; then 010 H3, 020 N1.
- F1-B closed (C-94). M4 stage 3 complete (C-91).
- Plan: `M3_NIGHT_PLAN_20261005.md`.
