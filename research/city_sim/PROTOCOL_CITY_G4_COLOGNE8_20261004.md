# PROTOCOL G4-TV: second network (RESCO cologne8) for T1, T4 and T5 (registered 10:14 04/10/2026, before any training or evaluation on cologne8)

**Assets.** RESCO cologne8: 8 lights, TAPAS demand 07:00–08:00, a single route file. CC BY-NC-SA, kept in `external_assets/` (excluded from git), never redistributed. Download approved by the user ("RESCO thì ok"). Route variants are written to `external_assets/RESCO_variants_20261004/`. RESCO ships one demand, so episodes differ only by SUMO `--seed` (driver imperfection, departure details), and the "traffic seed" here is the SUMO seed.

**Lights.**
- FT: the net's own static programs (the RESCO fixed-time baseline). ACT is not available on this net without conversion, so T1 is tested against FT here, not ACT.
- RLK: a learned keep / advance-over-all-greens light (`CITY_lightk.LightRLK`), trained by `CITY_g4_train_light.py` (sha 345ff3bb…, unchanged since 08:47) with all-SUMO traffic. 120 episodes, SUMO seeds 0–7, DQN seeds 11 and 12 (two light seeds).

**Fleet.** Membership: the same `_stable_u(seed, vid) < 0.5` as grid4. Arms:

| Arm | Agent cars |
|---|---|
| base | the original file (all `pkw`, Krauss σ 0.5) |
| sig0.3 | `setImperfection(v, 0.3)` at departure |
| ctrl | route variant with an identical copy vType (identity check) |
| acc | route variant with `carFollowModel="ACC"` (pkw attributes kept) |

**Evaluator:** `CITY_g4_eval.py`. Tripinfo with unfinished trips, scenario 25200–28800.

**Evaluation seeds:** SUMO 100–109 (disjoint from training 0–7).

**Readings** (crossed light-seed × seed, 2000 draws, rng 0, one-sided 95 %):

| # | Reading |
|---|---|
| G4-0 | Self-check: ctrl ≡ base exactly under every light. Otherwise void. |
| G4-1 (T1) | RLK − FT city TL with base traffic. "The learned light beats FT" iff upper < 0. |
| G4-2 (T4) | σ 0.3 interaction: [(sig0.3 − base) \| RLK] − [(sig0.3 − base) \| FT] on city TL. NO HARM iff upper < +0.5. |
| G4-3 (T5) | ACC interaction, same form. NO HARM iff upper < +0.5. |

Also reported: agent / human TL, agent fuel %, teleports, unfinished.

**Predictions:**
- G4-1: unknown. The learned controller is new on this net.
- G4-2 / G4-3: NO HARM, as on grid4 (C-30, C-32 … C-34).

**Reading if G4-1 fails.** The light "upgrade" on cologne8 is then not beneficial. G4-2 / G4-3 still answer whether the frozen learned light hurts an upgraded fleet, but they are labelled "under a non-beneficial light".
* Freeze (10:15): job 055 d795d9effa06; CITY_g4_eval 88423cac5be8b7b5; CITY_g4_make_variants 89e6f3f6ac11e71a; CITY_g4_report 09b12f4366b809b6; CITY_g4_train_light 345ff3bb61c105cc; CITY_lightk e5c63e5752db335e. Disclosure: a 300 s FT smoke on SUMO seed 100 (all four fleet arms) was seen; ctrl ≡ base.
### Result (10:19): G4-0 PASS; G4-1 NOT SUPPORTED (+4.79); G4-2 / G4-3 HARM NOT EXCLUDED (underpowered, sd ≈ 3 per seed). Ledger C-35.

## G4-L2 (registered 10:20, after G4-TV; the budget change is post hoc)

**Why.** G4-1 failed: the 120-episode RLK is worse than FT. The cheapest check is whether the budget is the reason.

**Lights.** RLK DQN 11 / 12 at **480 episodes**, same trainer, names RLK480_s11 / s12.

**G4-1'.** RLK480 − FT city TL on SUMO seeds 100–109 (base traffic only; FT rows reused from `eval/`). "Beats FT" iff the one-sided upper < 0.

**Gate.** Only if G4-1' holds: T4 / T5 are re-tested with RLK480 on 20 FRESH SUMO seeds 110–129 (G4-2' / G4-3', the same no-harm criterion, upper < +0.5), plus FT on those seeds. Otherwise G4 stops here and the reading is "the grid4 light recipe does not produce a beneficial light on cologne8 at 120 or 480 episodes".

Job 056.
* G4-L2 freeze (10:20): job 056 c99e62c8eb2d; CITY_g4_report2 edebbb5adef26fb7
### G4-L2 result (10:29): G4-1' NOT SUPPORTED (+15.10); G4 stops (ledger C-36).
