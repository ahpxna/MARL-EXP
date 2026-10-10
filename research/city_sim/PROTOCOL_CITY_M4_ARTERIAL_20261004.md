# PROTOCOL — M4: an independent second setting, RESCO arterial4x4 (04/10/2026 20:21; stage 1 registered before any arterial4x4 run)

Milestone M4 of `TWO_POPULATION_PAPER_FINISH_LINE_20261004.md`: "a working learned-light baseline on an independent network first". cologne8 failed with the grid4 light recipe (C-35 / C-36).

**Setting.** RESCO `arterial4x4`:
- third-party benchmark (GPL-3 code, CC BY-NC-SA scenario, kept in `external_assets/`, never redistributed);
- 16 signals; 80 edges of 65–186 m, half 1-lane and half 2-lane;
- FT program of **5 greens × 10 s + 5 yellows × 3 s** (65 s cycle);
- 1 000+ route files from RESCO's generator.

**Traffic split by route file:**
- TRAIN = arterial4x4_1…8;
- DEV = 100…109;
- fresh confirmation = 1000…1019 (never opened before its stage).

Route files are extracted from the zip into `external_assets/RESCO_variants_20261004/arterial4x4/` (local only).

**Stage 1: learned-light baseline.**
- **Light:** `CITY_lightk.LightRLK` (shared-parameter keep / advance over ALL greens; the RL-H analogue for multi-green programs). Q7 DQN (7 → 64 → 64 → 2), γ 0.9, the Q7 ε schedule, 200 updates per episode, halting reward. **120 episodes**, TRAIN files in rotation, SUMO seed = file index, 3 600 s.
- **Seeds:** DQN 11 and 111 (pilot).
- **Comparators:** FT (the net's programs) and MaxPressure (`CITY_eval4` MP adapted to all greens only if needed; otherwise reported as not applicable).
- **Evaluation:** DEV files 100–109, all-SUMO traffic (σ 0.5).

**Endpoints** (city TL, s/veh; teleports and unfinished reported):
- **M4-1:** RLK − FT, upper < 0, for EACH seed.
- **M4-1′ (descriptive):** RLK − MP.

**Checks:**
- **K4-0:** an episode with LightRLK holding the FT program (never advancing) is not used. Instead: the FT evaluation of the net is run twice and is bit-identical (determinism).
- **K4-1:** a 300 s smoke of the trainer.

**Predictions:**

| # | Prediction |
|---|---|
| P-M4-1 | RLK beats FT on arterial4x4 for both seeds. FT has 10 s greens on all 5 phases, which is poor for an arterial with dominant through flows. Prior: moderate, given cologne8's failure. |
| P-M4-2 | If M4-1 fails, the failure mode is the reward. The registered single fix is then a PRESSURE reward (incoming − outgoing halting), same everything else, 120 episodes. |

**Later stages** (registered when stage 1 passes):
- **Stage 2:** the SPaT fleet on arterial4x4 under FT, i.e. the R8 rule GLOSA-L∘σ\* and the R9 4-parameter search. This repeats M1 cheaply.
- **Stage 3:** the M2 matrix (FT → RLK; labelled / naive / forecast).
- **Stage 4:** the M3 method (whichever is confirmed on grid4).

## Amendment M4-A1 (20:23, before any learned-light run on arterial4x4)

**Finding.** The FT smoke on DEV file 100 (one file, FT only, disclosed) gives city TL **929 s/veh** with **214 / 1 931 trips unfinished** at 5 400 s. At the full RESCO demand, arterial4x4 is heavily oversaturated under the FT program. SPaT eco-driving has no meaningful role in oversaturation (Xin et al. 2019, NYSDOT / FHWA report), so the full-demand setting cannot host M1–M3.

**Registered thinning rule** (chosen on TRAIN files only):
- A vehicle is kept iff u(vid) < p, with u = the `CITY_env._stable_u` hash with seed 0, independent of the file.
- p is the LARGEST value in {0.3, 0.4, 0.5, 0.6, 0.7} such that FT, on all 8 TRAIN files 1–8, gives city TL ≤ 60 s/veh AND 0 unfinished.
- The chosen p is applied to every file (TRAIN, DEV, confirmation).
- The setting is reported as "RESCO arterial4x4 geometry and route structure, demand thinned to p".

Nothing else in stage 1 changes.

### M4-A1 result (20:24)
FT on the thinned TRAIN files 1–8 (`m4_20261004/thin/FT_p*.json`): city TL stays at about 500–800 s/veh even at p = 0.3 (720 vehicles per hour), and unfinished trips appear from p = 0.6. **No p satisfies the registered rule** (TL ≤ 60, 0 unfinished). The pathology lies in the RESCO arterial4x4 FT program (5 greens × 10 s), not in the demand level alone.

Per the rule, **arterial4x4 as registered is NOT a viable M4 setting**. No tuning of the FT program is attempted, because that would be an unregistered change of the base controller.

**Next:** Amendment M4-A2, an own-built independent network (separate registration).

## Amendment M4-A2 (20:24): an own-built independent network, "spider" (registered before generation)

**Network.** `netgenerate --spider` with 6 arms, 3 circles, 150 m ring spacing, the center omitted, and `--tls.guess`. It has radial and ring streets, intersections of degree 3–4, and a topology unlike a grid. Default SUMO static TLS programs; 1 lane per direction. Built locally into `research/city_sim/net/spider.net.xml`.

**Admissibility check (before any learning):** every TLS program has exactly 2 greens, so the RL-H class applies. Otherwise LightRLK is used.

**Demand.** randomTrips with the grid4 configuration (fringe-factor 10, min-distance 300, vehicle-class passenger; seed = file index).
- The period is chosen on TRAIN seeds 0–7 only: the SMALLEST period (largest demand) in {1.5, 2.0, 2.5, 3.0, 4.0} s with FT city TL ≤ 60 s/veh and 0 unfinished on all 8 TRAIN seeds.
- DEV seeds 100–109; fresh confirmation 1000–1019, generated only at their stage.

**Stage 1 (unchanged otherwise):**
- the RL-H recipe on spider: Q7 `train` semantics, 2-green keep / switch, halting reward, 120 episodes, DQN seeds 11 and 111;
- **M4-1:** learned light − FT city TL, upper < 0 for each seed (DEV 100–109);
- **P-M4-1** prior: moderate. The fix in P-M4-2 (pressure reward) stays the single registered fallback.

### M4-A2 result and Amendment M4-A3 (20:28)

**Spider net built:** 18 TLS. 12 have 2 greens (42 / 3 / 42 / 3) and **6 have 3 greens** (27 / 3 × 3). The 2-green admissibility check fails, so **LightRLK** (keep / advance over all greens) is used, as registered.

**FT on spider TRAIN 0–7:** p1.5: mean TL 106.7, unfinished 0; p2.0: mean TL 95.1, unfinished 0; p2.5: mean TL 89.6, unfinished 0; p3.0: mean TL 86.1, unfinished 0; p4.0: mean TL 80.6, unfinished 0; 
- **No period satisfies the registered TL ≤ 60 rule.** Even the lightest demand gives about 82 s/veh, because routes are longer and cycles 90 s.
- The absolute threshold was set with grid4 in mind and does not transfer.

**M4-A3 (post-check, declared):** use the grid4 demand configuration unchanged, **period 2.0**.
- This choice does not depend on the spider numbers. At period 2.0, FT gives 0 unfinished trips and its TL is moderately above the lightest demand (about +16 %), so the network is not oversaturated.
- DEV seeds 100–109 and confirmation seeds 1000–1019 are generated at period 2.0 when their stages open.

**Stage 1 now runs on spider with period 2.0:** LightRLK, Q7 DQN, halting reward, 120 episodes, DQN seeds 11 / 111; M4-1 vs FT on DEV.

## Stage 2 on spider: M1 replication (registered 20:31, before any spider fleet run; it runs only if M4-1 passes)

**Tooling.** `CITY_m4s_run.py` patches Q7.NET_S, Q7.ROU and TRAIN_SEEDS to spider, then runs the unchanged grid4 scripts. Check **K4-2:** FT city TL from `CITY_eval4` via the runner equals `CITY_m4g_eval` FT on seed 100 (bit-identical).

**2a, the rule GLOSA-L∘σ\*** (same code as R8; spider has 1 lane per direction, so the lane-aware release is trivial). On DEV 100–109, vs always-SUMO (a) and vs σ\* (b), with the R8 endpoints.
- **Prediction P-M4-2a:** (a) and (b) on fuel hold, but **human TL may fail**: on 1-lane roads, followers cannot pass a slowing GLOSA car. The prior for passing human NI is low.

**2b, R9 4-parameter search** (`CITY_glosa_lane_d search`) on spider TRAIN 0–7, search seeds 1–5:
- pilot seed 1 on DEV: gate (a) AND (d″) vs the rule;
- confirmation: pooled seeds 2–5 on FRESH spider seeds 1000–1019 (generated at the gate) with (a), (b) and (d″).
- **M1-spider is MET** if the confirmation passes all three, i.e. the R9 rule of C-54 replicated.

## Amendment M4-A4 (21:04, 04/10): 2b evaluation details (registered after the search, BEFORE any 2b evaluation)

**Search.** All five searches finished at 21:01:58. θ_s1 = [0, 2.32, 154.5, 200], training J −7.54 (the rule θ_L: −5.76). The training J is never an endpoint.

**Pilot.**
- Directory `spider/s2b/eval_dev`, DEV 100–109 (the 2a seeds), FT light. The candidate is ESLD_s1 (`CITY_eval6_lane2.py --fleet ESLD:theta_s1.json`).
- The comparators are RE-RUN in the same directory with the same code as 2a: GLOSALS (the rule), OFF_FT (always-SUMO), and S0.0…S0.4_FT (the σ family, for labels).
- Gate: exactly the R9 rule of `CITY_lane_d_report.py`, i.e. (a) vs always-SUMO (the R8 endpoint, `a_pass`) AND (d″) vs the rule (fuel upper < 0, agent TL upper < +0.5, human TL upper < +0.5, teleports ≤ rule + 1). On a pass the report writes `GATE_PASS`.

**Confirmation (only if GATE_PASS).**
- First generate spider p2.0 seeds 1000–1019 with the identical randomTrips command (checked beforehand by regenerating seed 100 into scratch and comparing it with the existing file).
- Then pooled ESLD_s2..s5 (crossed fleet-seed × traffic) with (a), (b) vs σ* 0.3, and (d″), plus per-seed (d″).
- **M1-spider MET** iff (a), (b) and (d″) all pass.

**Code.** New and unfrozen until launch: `scripts/CITY_m4_s2b_report.py` and `research/city_sim/m4_20261004/spider/RUN_s2b_eval.sh`. Hashes are recorded at launch.

**Prediction P-M4-2b.** The pilot passes (a); for (d″), training J says about 1.8 points better than the rule, but on grid4 R9 delivered −2.8 %. Prior for (d″): moderate.
* 21:04 — **Frozen at the pilot launch:** CITY_m4_s2b_report.py f5d67227f32faf65; RUN_s2b_eval.sh 03ddfe6234df1d8e; CITY_eval6_lane2.py 5b65ee1dec079db6; CITY_glosa_lane_d.py 3295a2bbefb1b260; CITY_m4s_run.py d7c22c9f58f784ab; 

## Amendment M4-A5 (21:15, 04/10): stage 3, the M2 matrix on spider (registered before any stage-3 run)

**Populations (all frozen).**
- L0 = FT, the spider static programs.
- L1 = RLK_sp11 and RLK_sp111, the two stage-1 lights (M4-1 PASS, C-76). They are reached in the E4 stack by a call-time patch of `CITY_eval4.build_light` for the spec `RLK:<ckpt>` → `CITY_lightk.LightRLK`. LightRLK holds greens with setPhaseDuration(1e5) and advances through the program's yellow, like RL-H.
- **F0 = the rule GLOSA-L∘σ\*** (`GLOSAL:0.3`), the only spider fleet that passed its stage (2a PASS; 2b R9 FAILED at the pilot, C-80). There is no learned fleet on spider; this is declared.
- References: OFF (all SUMO, σ 0.5) and σ\* 0.3.

**SPaT arms under L1 (as M2):**
- **naive:** the fleet uses `CITY_spat_feature.spat` (program-derived; `unavailable` while a green is held; a mislabelled program forecast during yellows).
- **labelled:** the light publishes no SPaT, so the fleet falls back to σ\*.

**Forecast arm:** NOT run on spider. The empirical forecast (CITY_spat_forecast and the corrected version) models a two-green cycle (green → yellow → the other green); 6 of the 18 spider lights have three greens. A forecast there would need new modelling, which M4 does not register. This is declared as a scope limit.

**Panel.**
- Fresh spider p2.0 traffic 1000–1019. These were reserved for the 2b confirmation, which was not evaluated (C-80), so they are unused. They are generated now with the verified command (seed 100 was regenerated identically, M4-A4), and KA-type check: they must not exist before generation.
- Pairs: light j ∈ {sp11, sp111}. OFF and σ\* run under each light; under FT, OFF / σ\* / F0 are single rows.
- Cubes [light 2, traffic 20]; crossed bootstrap 2 000 draws (the M2 code: `fm`, one-sided 95 % bounds).

**Endpoints (= M2):**
- **M2-A:** RLK − FT with OFF and σ\* cars (city TL, city fuel %). The upgrade must be beneficial (OFF city TL upper < 0) for the DiD to be read.
- **M2-B:** F0 − σ\* under each light and arm (agent fuel %, agent TL, human TL).
- **M2-C:** DiD on agent fuel %. LOST if the one-sided lower bound > +1; KEPT if the upper bound < +1.
- **M2-D:** valid-SPaT share.
- **M2-E:** no harm under L1 (F0 − σ\* agent and human TL upper < +0.5).

**Checks (exit 1), on spider DEV seed 100 (rows from 2a exist there):**
- **KM4-3a:** OFF through the M2 wrapper under FT ≡ the 2a OFF_FT row (bit-identical).
- **KM4-3b:** F0 through the M2 wrapper under FT, naive ≡ labelled ≡ the 2a GLOSALS row.
- **KM4-3c:** under RLK_sp11, labelled F0 ≡ σ\* (eval4_sigma 0.3 through the same runner), bit-identical.
- **KM4-3d:** naive under RLK_sp11 has ≥ 1 valid SPaT call. Otherwise the mislabelling concern is void, and that is reported.
- **KM4-3e:** the RLK patch is live: OFF under RLK_sp11 differs from OFF under FT.

**Predictions.**
- **P-M4-3-1:** M2-A beneficial; stage 1 measured about −57 s/veh in the generic evaluator.
- **P-M4-3-2:** labelled → F0 rows identical to σ\*, so DiD ≈ the whole FT benefit (about +9 points), LOST, no harm. This replicates M2a on a second network.
- **P-M4-3-3:** naive → LOST. Harm is possible. On grid4 the naive frozen fleets were harmed (+7.4 / +6.5 % fuel vs σ\*). On spider, the prior for harm is moderate.

**Reading.** If P-M4-3-2 / 3 hold, the compatibility problem of M2 (a frozen SPaT fleet loses its benefit when the light is upgraded, and is harmed if it trusts a stale program) is replicated on an independent network, with a different light architecture (all-green LightRLK) and a different fleet (the rule).
* 21:16 — **Frozen at launch:** CITY_m4s_rlk.py fefd5ec87be28038; CITY_m4_s3_check.py 0101954c88ebbc1d; CITY_m4_s3_report.py 1047626833e0807a; RUN_s3.sh d3e229e5b46b7438; CITY_eval6_m2.py d1b00bd0173ddc53; CITY_eval4_sigma.py c277775c606529b2; CITY_lightk.py e5c63e5752db335e; CITY_m2_report.py a06cdf591bcd9a1b; 

## Amendment M4-A6 (21:26, 04/10): stage 4, re-running the M3 main comparison on spider (registered BEFORE the M3-NC and F1-A1 results)

**4a. Light-side commitment with the frozen fleet (M3's main comparison; replication of the M3-NC question).**
- **Light WCK-W** (`CITY_m4s_wck.py`, new):
  - RLK_sp11 / sp111 decides advance / keep exactly as LightRLK.
  - An advance decided at t is EXECUTED at t + W (the green is held meanwhile; no new decision while pending). W = 5, the grid4 DEV-selected W (no tuning here).
- **SPaT** is commitment or `unavailable` (the clean RPC-style message; the forecast fallback of grid4 WC5 is undefined for three-green lights).
  - While pending at a light: links served by the current green get ttr = t_e − t.
  - Links served by the NEXT green in cycle order get ttg = t_e − t + Σ(durations of the program's non-green phases between the two greens) + OBS.
  - Every other link gets `unavailable`.
- **Fleet:** the frozen rule GLOSA-L∘σ\* (`GLOSAL:0.3`).
- **Panel:** spider 1000–1019, re-used. The stage-3 rows are on it; no stage-4 choice was ever made on it, and W comes from grid4.
  - R = the stage-3 labelled rows (identical to σ\*).
  - Shadow = WCK-5 with σ\* cars (W-c is fleet-blind).
- **Endpoints:**
  - M3-1: agent fuel % vs R, cube [light 2, traffic 20], crossed.
  - M3-4clean: shadow − σ\*-under-RLK.
  - M3-3clean: fleet − shadow.
  - TL reported.
- **Decision:**
  - NEGATIVE REPLICATED iff the M3-1 one-sided lower bound > 0.
  - Positive iff the upper bound < 0 (reported; contradicts grid4; no claim without its own confirmation).
  - Otherwise NOT SHOWN BETTER.
  - Reason named as in M3-NC.
- **Checks (exit 1, spider DEV seed 100):**
  - **KW-1:** WCK with W = 0 under σ\* cars ≡ RLK under σ\* cars (bit-identical rows).
  - **KW-2:** every executed commitment's green END equals t_e (from the light's own log).
  - **KW-3:** every promised green ONSET (t_e + Σ non-green + OBS) equals the observed onset at that light. The (observed − promised) distribution is printed. If it is a constant offset ≠ 0, the formula's OBS is corrected ONCE before the panel and the check re-run (declared, as in M3 S5); otherwise stop.
  - **KW-4:** the fleet receives ≥ 1 valid commitment.
- **Prediction P-M4-4a:** NEGATIVE REPLICATED (grid4 DEV WC5 +3.6 %, RPC +9.4 %). Prior: moderate. On spider the rule's FT benefit is larger (−9 %), so exact timing may help it more.

**4b. The retrained-fleet reference (only if F1-A1 is CONFIRMED).** Not designed yet. A forecast for three-green lights needs modelling that is not registered. If F1-A1 confirms, 4b is registered separately before any 4b run. If F1-A1 does not confirm, 4b is not run.
* 21:28 — **Checks (spider seed 100):**
  - KW-1 PASS (WCK W = 0 and RLK through the new wrapper ≡ the stage-3 labelled row, bit-identical).
  - KW-2 PASS (2 394 executions, green-end error 0).
  - KW-3 PASS (2 394 onsets, observed − promised = 0 on all; 0 into an unexpected green; no OBS correction needed).
  - KW-4 PASS (13 811 valid commitment calls).
  - **Smoke disclosed before the panel (seed 100, not an endpoint):** WCK-5 + rule vs the labelled row: city TL 45.7 vs 34.6, agent fuel +8.2 %.
  - **Frozen at launch:** CITY_m4s_wck.py fdc3d9f18c74c23f; CITY_m4_s4a_report.py 5bc79cb1dde7ddb5; RUN_s4a.sh 3b9ea4c061a40656; 

## Amendment M4-A7 (21:34, 04/10): stage 4b design, registered BEFORE the F1-A1 result; run ONLY if F1-A1 is CONFIRMED

**Provider: `CITY_spat_forecast_k` (new).**
- A multi-green empirical forecast. Greens and non-green program time come from NetInfoK; the convention is corrected in EVERY branch, including the C-84 branch. Links served by the current AND the next green get `unavailable`.
- Fitted per light on spider RLK traces with σ\* cars, TRAIN 0–7 (`spider/s4b/traces`, recorded 21:33).
- **Declared deviation from grid4:** the table is open-loop. Spider has no deployed learned fleet to drive the closed-loop prep.
- q = 0.1, the F1-locked value, not re-selected.

**Trainer: `CITY_fleet_train_f1k.py` (new).** The CITY_fleet_train_f1 recipe unchanged (v11 PPO speed residual on GLOSA-L∘σ\*, zero init, 200 episodes, spider TRAIN 0–7), with the light LightRLK(sp k) frozen and the forecast-K provider at q 0.1. Seeds 213 / 313 under sp11, 413 / 513 under sp111.

**Panel.**
- Fresh spider 1020–1039, generated after a non-existence check.
- Crossed over 2 lights × 4 fleets × 20 traffic (bootstrap over light, fleet and traffic).
- R = RLK + no SPaT with the rule (≡ σ\*, KW-1 / KM4-3c).
- RULE reference = the zero residual (`RULE0_fleet.pt`) with forecast-K.

**Gate (= F1 §3), F1k pooled vs R:**
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports ≤ R + 0.1;
- unfinished ≤ R.

**F1-SPIDER CONFIRMED** iff all of these pass.

**Checks (exit 1):**
- **KK-1:** the forecast-K convention check on ALL 16 trace files shows 0 error in every branch, and its negative control (no +1 for intermediate greens) FAILS. Already run on 3 files at 21:38: PASS, and the negative control fails as required.
- **KK-2:** the training light's sha equals RLK_sp<k>.pt.
- **KK-3:** the evaluator with fleet RULE0 and SPaT none ≡ R rows (bit-identical, one seed).
- **KK-4:** 1020–1039 did not exist before generation.

**Predictions.**
- P-4b-1: RULE with forecast-K is worse than R in fuel (grid4: +3.28 %).
- P-4b-2: F1-SPIDER is confirmed. Prior LOW to moderate: on spider R9 did not beat the rule, the rule's TL parity is marginal, and the roads are single-lane.
* 21:39 — **4b prepared (not launched):**
  - KK-1 PASS on all 16 traces: 0 error in all six branches, including the C-84 branch and the three-green chains. Its negative control FAILS as required (`s4b/check/kk1_*.txt`).
  - KK-3 PASS (RULE0 + none ≡ rule + none ≡ the stage-3 labelled row, seed 100).
  - Smoke: 1 training episode plus a forecast-K evaluation run.
  - Tables fitted: 18 lights × 8 files each.
  - RUN_s4b.sh exits by itself unless F1-A1 is CONFIRMED.
  - **Frozen:** CITY_spat_forecast_k.py 7848a3f3219b83dc; CITY_spat_forecast_k_conv.py 6cf21dd2c977c9a7; CITY_fleet_train_f1k.py 7ee3b5b609cd80c5; CITY_m4s_f1k_eval.py 34d82814491ad12f; CITY_m4_s4b_report.py cc02cc6a4c1143a2; RUN_s4b.sh 10aabebfd7e408ba; fk_rlk11.json df0bacf1ba818759; fk_rlk111.json 12e137ea47ff2ad7; 

## Pointer (22:11, 04/10): stage 3 completed design → `PROTOCOL_CITY_M4_STAGE3_20261004.md` (3b forecast arm with forecast-K + DEV q selection; 3c the adapted-fleet column, descriptive). 3a (C-81) unchanged.
