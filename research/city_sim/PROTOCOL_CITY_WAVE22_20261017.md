# PROTOCOL W22: can the fleet's owner detect, from its own data, that a learned signal responds to its vehicles, and does a per-vehicle A/B test measure the forecast's harm? (registered 17/10/2026, 00:5x EDT, before any W22 run)

**User (16–17/10/2026):** after "có thể nghiên cứu hướng nhân quả của project này ko?", a reading of the original CIG-AMF papers and a collision search (`research/papers/audits/NOVELTY_CAUSAL_W22_20261017.md`): "làm các bước đầu đi".

**Why.** The CIG-AMF papers (`cig_amf/docs/Paper_A_Causal_Influence_Spectrum.tex`, `Paper_B_CIG_AMF_Core_Periphery.tex`) measure inter-agent influence by intervention:
- sparse randomised action forcing with a known propensity;
- the structural capacity C (how far another agent's outcome can be moved), kept separate from the behavioural direction D.

The signal upgrade is a structural shift of exactly this kind:
- Under fixed time, the fleet's driving has no influence on the timing: C(fleet → signal) = 0.
- Under a stop-thresholded learned signal it has (W19, W20).

The paper's check, "see what the signal counts", needs the signal's internals, and a separately owned fleet does not have them. Two questions follow:
- **D1.** Can the owner identify C(fleet → signal) from its own randomisation, using only what it can observe?
- **D2.** If the owner evaluates SPaT use by the usual per-vehicle A/B test, is the estimate of its harm biased? The signal responds to the treated vehicles, and its response reaches the control vehicles (interference through a responsive controller).

## Setting

- **World:** grid4, Krauss drivers, the W20 setting: `CITY_w9_run.py none → CITY_w20_run.py → [W22 wrapper] → evaluator`, PYTHONHASHSEED=0, OMP_NUM_THREADS=1.
- **Families,** with ground truth from the same setting (W19, W20 rows on fresh days 1400–1419):
  - **RMP** (MPLight, t94–t98): strongly exposed. SV − R agent time loss +16.02 s/veh; mean green 15.89 → 20.68 s.
  - **AH** (t34–t38): weakly exposed. +1.70; 14.73 → 16.40.
  - **RWV** (`wave`, t99–t103): threshold-free control. −1.05; 9.68 → 9.71.
- **Fleets:** FRESH3 s1413 and s1513. **Days:** 1400–1409.
- **SPaT:** each light's deployed service at q 0.1. Provider files: W19 for AH, W20 for RMP and RWV.

**Wrapper** `scripts/CITY_w22_assign.py` (no file edited): the provider answers every query; a control vehicle ignores the answer and is released to its base driver, as under no SPaT.
- **MIX50,** per vehicle: `W22_ASSIGN=veh:0.5`. Fleet vehicle v uses SPaT iff u('veh', day, v) < 0.5.
- **SWB,** switchback per light: `W22_ASSIGN=swb:300:0.5`. During window w = ⌊t/300⌋, fleet vehicles use the SPaT of light j iff u('swb', day, j, w) < 0.5.
- **Probe** (`W22_PROBE=1`, read-only), per (light, 300-s window): count and summed duration of greens, overall and for greens starting at least 60 s into the window (burn-in against carry-over); fleet vehicles on the light's red links during those greens; the window's assignment.

## Checks (must pass before any result is read)

- **KW22-1:** `W22_ASSIGN=all` with the probe on reproduces the SV rows. Cells: t94 s1413 days 1400–1401 (W20) and t34 s1413 days 1400–1401 (W19). Fields: time losses, fuel, counts, teleports, unfinished, action digest.
- **KW22-2:** `W22_ASSIGN=none` with the probe on reproduces the R rows of the same cells.
- **KW22-3:** in MIX50 the treated share among fleet vehicles is within 0.5 ± 0.05 over the panel, and withheld queries > 0. In SWB the treated window share is within 0.5 ± 0.05.

If KW22-1 or KW22-2 fails, nothing is reported. The cause is found and the check rerun; the failed attempt is kept.

## D1: owner-side identification (SWB)

**Observable to the owner:**
- the signal's phase changes, which every fleet vehicle sees;
- its own assignment;
- its own vehicles.

The signal's inputs, rewards and programs are not used.

**Statistic:** per light-day, τ = (mean green duration in treated windows) − (mean in control windows), over greens starting ≥ 60 s into a window. Averaged over lights × fleets × days within a family.

**Test:** Fisher randomisation. Under the sharp null "the signal's greens do not depend on the fleet's SPaT use", the green records are fixed, so window labels are re-drawn (Bernoulli 0.5 per light-window, 2 000 draws, salt `fisher<k>`) and τ is recomputed. The test is one-sided (τ > 0), at α = 0.05 / 3 per family.

**Registered reading, per family:**
- "the owner detects the response" if τ > 0 and p < 0.0167;
- "not detected" otherwise.

**Predictions:** RMP detected; RWV not detected; AH uncertain (small response).

**Also reported (descriptive):**
- τ against the ground-truth green change SV − R from the W19 / W20 rows on the same lights, fleets and days. τ is a partial-exposure estimate, so it is expected to be smaller than SV − R.
- a 95 % crossed bootstrap of τ.

## D2: interference bias of a per-vehicle A/B test (MIX50)

- **Naive estimate,** per run: DM = mean agent time loss of treated fleet vehicles − that of control fleet vehicles.
- **Target:** the global effect GTE = SV − R (agent time loss), from the W19 / W20 rows on the same light, fleet and day.
- **Bias** = DM − GTE, with a 95 % crossed bootstrap over lights × fleets × days (2 000 draws, seed 0).
- **Spillover on the control vehicles,** described: TL_C(MIX50) − R and TL_T(MIX50) − SV.

**Registered reading, per family:**
- "the per-vehicle A/B test misestimates the harm" if the bias interval excludes 0, with the sign reported;
- otherwise "no bias shown".

**Predictions:**
- RMP: bias < 0, i.e. the A/B test understates the harm, because the lengthened greens and the later service fall on control vehicles too.
- RWV: no bias shown.
- AH: uncertain.

## Size, smoke, order

- **Panel:** 3 families × 5 lights × 2 fleets × 2 arms = 60 jobs × 10 days = 600 grid4 episodes, about 15–25 min with 6 lanes.
- **Smoke:** one RMP light, one fleet, one day, `--smoke`, through both arms and the report, before the checks and the panel.
- **Order:** smoke → KW22-1 / KW22-2 (8 runs × 2 days) → panel → report.
- **Outputs:** `research/city_sim/w22_20261017/`. The report script is `scripts/CITY_w22_report.py`.

## What this does not test

- Real detectors, real fleets and partial penetration other than this fleet's share.
- D1 identifies the response to the fleet's SPaT use, not which input causes it. W19 did that with the internals.
- A switchback design for D2 (network-wide windows) is left for an amendment, registered before it runs.

## Clarifications (17/10/2026 01:0x, after the smoke and KW22-1 / KW22-2, before any panel run)

- **KW22-1 and KW22-2 passed.** `W22_ASSIGN=all` and `none`, with the probe on, reproduce the SV and R rows bit for bit on t94 s1413 and t34 s1413, days 1400–1401: time losses, fuel, counts, teleports, unfinished, action digest and mean green. Rows are in `w22_20261017/check/`.
- **"Light" in D1** means each of grid4's signals under the family's policy k. τ is computed per run and per signal over signals that have both treated and control greens. The run τ is the mean over signals; the family τ is the mean over runs (k × fleet × day).
- **Fisher labels** are drawn from numpy `default_rng(1)` (Bernoulli 0.5 per signal-window and draw), not from a hash salt. Validity under the sharp null is unchanged. The report asserts that its vectorised τ equals the per-run τ.

## Result note (17/10/2026 01:10, after the panel; ledger C-256)

- KW22-3 passed.
- **D1:** detected for RMP, AH and RWV. **The registered prediction "RWV not detected" failed.** RWV's τ is +0.10 s, z 2.9 against a randomisation sd of 0.036 s. Its sign flips without the 60-s burn-in (−0.04). The sharp-null test detects the existence of a response, not its size. An exposure decision needs a size threshold, which was not registered and is not applied here.
- **D2:**
  - RMP: understates, as predicted.
  - AH: overstates (prediction "uncertain").
  - RWV: no bias shown, as predicted.

## Amendments W22-A, W22-B, W22-C (17/10/2026 02:0x, before any of their runs)

**User (17/10):** "làm cả 3 bước tiếp theo đi". The three steps proposed after C-256:
1. a size-based decision rule for D1, with its cost;
2. a treated-share sweep and an alternative design for D2;
3. a replication in the W17 field-matched world.

**Battery guard (all three):** no new job starts while the Mac is discharging at ≤ 20 %. Re-running resumes, and a report runs only on a complete panel.

**Order:** W22-C, then W22-A, then W22-B.

### W22-A: deciding exposure by size, and what the test costs the fleet (grid4, fresh days 1410–1419, never used in W22)

- **Threshold:** δ = 0.5 s of mean-green lengthening, the paper's 0.5 s/veh limit scale. **Chosen after seeing W22's τ values** (RWV +0.10, AH +1.69, RMP +3.85). It is therefore evaluated only on days 1410–1419 and in W22-C, which no W22 analysis has touched.
- **Arms:** SWB at treated-window share p ∈ {0.5, 0.8, 0.95}, i.e. the owner forgoes SPaT in a share β = 1 − p of signal-windows. Tags `SWBp50`, `SWBp80`, `SWBp95`. Families RMP, SRL (t84–88), RDQ (t89–93), AH, RWV; fleets s1413, s1513; 5 lights each.
- **Decision unit:** one deployed policy k with one fleet, 10 units per family. Per day d, τ_d = mean over signals of (treated − control mean green), with greens starting ≥ 60 s into a window.
- **Rule, after n = 2…10 days:** Student-t 95 % interval of the mean of τ_d.
  - "exposed" if the lower bound > δ;
  - "not exposed" if the upper bound < δ;
  - otherwise continue.
  - Reported: the first n that decides, and its label. A normal-mixture confidence sequence with plug-in sd is also reported, descriptive and approximate.
- **Truth label per unit:** SV − R mean green over the same days > δ (W19 / W20 rows).
- **Cost:** fleet fuel and agent time loss of the SWB run against the SV run on the same light, fleet and day.
- **Registered predictions:**
  - at p = 0.5, every RMP / SRL / RDQ / AH unit is decided "exposed" within 3 days, and every RWV unit "not exposed" within 10 days, with no wrong decision;
  - the days needed grow as p → 0.95;
  - the fuel cost grows with β.

### W22-B: how the per-vehicle A/B bias depends on the treated share, and a design that should not be biased (grid4, days 1400–1409, as W22)

- **MIX arms:** p ∈ {0.1, 0.3, 0.7, 0.9}, tags `MIXp10` … `MIXp90`. W22's MIX is p = 0.5.
- **NSW arm** (new wrapper kind `nsw:600:0.5`): network-wide switchback, in which all fleet vehicles use SPaT during window w = ⌊t/600⌋ iff u('nsw', day, w) < 0.5.
  - Estimator: fleet time loss of trips departing ≥ 120 s into a treated window, minus the same for control windows.
- **Families:** RMP, AH, RWV; fleets s1413, s1513; 5 lights.
- **Bias(p)** = DM(p) − GTE and NSW − GTE, crossed bootstrap 95 %.
- **Registered predictions:**
  - RMP: DM(p) < GTE at every p, the gap largest at p = 0.1;
  - RWV: no bias shown at any p;
  - NSW: no bias shown for any family.

### W22-C: replication in the W17 world (every car the jointly calibrated W17-0 IDM)

- **Chain:** `CITY_w17_world.py → CITY_w9_run.py none → CITY_w20_run.py → CITY_w13_modes.py → CITY_w22_assign.py → CITY_eval_n4.py`, with W21-A's lights and forecasters (`w21_20261015/w17/`) and W17 FRESH5 fleets s2213, s2313. Days 1420–1429.
- **Arms:** SWB (300 s, p 0.5) and MIX (p 0.5); families RMP, AH, RWV.
- **Checks:**
  - KW22-C1 / C2: all / none with the probe = W21-A's SV / R rows, t94 s2213, days 1420–1421;
  - KW17-0: one world line per job;
  - KW22-3.
- **Ground truth:** W21-A's R / SV rows.
- **Readings:** as D1 and D2.
- **Predictions:**
  - D1: RMP detected; AH detected with a smaller τ.
  - D2: RMP bias < 0.
  - W21-A greens: MPLight +22.7 %, AH +4.3 %, wave −0.1 %.

## Result note W22-A / W22-C (17/10/2026 02:50; ledger C-257). W22-B incomplete (battery guard)

**W22-C:**
- Held: "RMP detected", "AH detected with a smaller τ", "RMP bias < 0".
- The switchback underestimates the global green change in this world.

**W22-A:**
- Held:
  - "no wrong decision at p 0.5";
  - "RWV not exposed within 10 days";
  - "days grow as p → 0.95";
  - "cost grows with the forgone share".
- Failed: "every exposed-family unit decided within 3 days". The maximum was 7 days, and two SRL units were correctly "not exposed" by their own truth.
- Not anticipated:
  - τ shrinks as the forgone share falls, through carry-over into rare control windows;
  - wrong decisions appear at p 0.95, all at n = 2.

## Result note W22-B (17/10/2026 03:55; ledger C-258)

- **Held:**
  - "RMP: DM(p) < GTE", shown for p ≤ 0.7 with the gap largest at 0.1. At p 0.9 the interval contains 0.
  - "RWV: no bias shown at any p".
- **Failed:** "NSW: no bias shown for any family", for RMP: bias −1.85 [−3.14, −0.63]. It held for AH and RWV.
- **Not anticipated:** AH overstates at every share, +1.25 to +1.59.

## Correction to the W22-A result note and C-257 (17/10/2026 12:4x; ledger C-259), found before any new run

**The finding "τ shrinks as the forgone share falls … carry-over" is withdrawn as stated.** Re-analysis of the existing W22-A rows (no new run) shows the shrinkage is mostly an estimator artefact, a length-biased ratio.

- The registered τ pools green durations per signal-day: sum of durations over sum of counts, i.e. weighted by the number of greens.
- At p 0.95 a signal-day has on average 0.58 control windows. Most signal-days are dropped. Where they are kept, one control window (its own mean) is compared with the pooled, green-count-weighted mean of about 11 treated windows.
- Within a window of fixed length, long greens mean few greens. So the green-weighted mean is below the window-weighted mean (Chebyshev's sum inequality), which biases τ downward when controls are rare.
- With a window-weighted per-day estimator (E2), or pooling each signal over the 10 days (E3, E4), τ is nearly flat in p, e.g. RMP 3.93 / 4.08 / 3.87 (E4). RWV's −0.43 at p 0.95 becomes −0.10 to −0.15.
- A residual shrinkage remains for RDQ (E4 2.28 → 1.79) and AH (1.57 → 1.42) at p 0.95. Its cause is not identified.

The W22-A decisions at p 0.95, including the wrong ones, used the biased estimator. A post-hoc re-analysis with E2 is reported separately and labelled post hoc; the registered table is kept.

## Amendment W22-D (17/10/2026 12:4x, before any W22-D run): longer, alternating network switchbacks for MPLight

**User (17/10):** "làm cả 3 hướng tiếp theo đi"; the first is the network switchback with longer windows and burn-in.

**Seen (C-258):** with 600-s Bernoulli windows the NSW estimate understated MPLight's global effect (−1.85 [−3.14, −0.63]) but not AH's or RWV's.

**Arms** (new wrapper kind `nswa:W`, alternating design):
- All fleet vehicles use SPaT in window w = ⌊t/W⌋ iff (w + b) is even, with b = 1[u('nswa', day) < 0.5]. Every day therefore has both kinds of window.
- **NSWa900:** W 900 s, burn-in 225 s.
- **NSWa1200:** W 1200 s, burn-in 300 s.
- Estimator as NSW: fleet time loss of trips departing ≥ the burn-in into a treated window, minus control windows.

**Panel:** families RMP, AH, RWV; fleets s1413, s1513; days 1400–1409; grid4 W20 setting.

**Checks:** KW22-0 again with the edited wrapper (all / none = SV / R; MIX row = W22's).

**Reading:** bias = estimate − GTE (SV − R agent time loss), crossed bootstrap 95 %.

**Predictions:**
- RMP's bias shrinks as W grows, and the NSWa1200 interval contains 0;
- AH and RWV show no bias in either arm.

**Size:** 3 × 5 × 2 × 2 = 60 jobs × 10 days, about 15 min.

## Result note W22-D (17/10/2026 12:55; ledger C-260)

- **Failed:**
  - "RMP's bias shrinks as W grows and the NSWa1200 interval contains 0": −2.71 at 900 s, −1.96 at 1200 s.
  - "AH no bias in either arm" fails at 1200 s: −0.71 [−1.38, −0.09].
- **Held:** RWV.
- **Not the design:** the alternating start bit was balanced 5 / 5 over the days.

## Amendment W22-E (17/10/2026 14:1x, before any W22-E run): predictions drawn from the post-hoc analyses

**User (17/10):** asked whether randomising by day or area or "something else" is better, to dig into "hides or exaggerates depending on the signal type, more so in small tests", what the five failed predictions teach, whether the data suggest new predictions, and why W17 underestimates.

**Seen, post hoc on existing rows** (`scripts/CITY_w22e_posthoc.py`, `e/report_w22e_posthoc.txt`, and the checks in this session's transcript):
- **Exposure mapping on switchback windows** (own window, own previous window, neighbours' share, plus own × neighbour; signal × run fixed effects):
  - on grid4 the local model reproduces the global green change: RMP 4.18 vs 4.19; AH 1.77 vs 1.51; SRL 2.21 vs 2.13; RDQ 2.20 vs 2.15;
  - in W17 it does not: RMP 2.97 vs 4.44; AH 0.05 vs 0.66.
  - The W17 gap is not the metric: the same window-weighted metric on the KC all / none rows gives +6.4 to +6.8 on that cell.
  - It is not accumulation over the hour: SV − R green is the same in the first and last thirds, +6.30 / +6.33.
  - It is not within-window lag: removing the burn-in leaves τ unchanged or larger in W17.
- **Run-level greens:** 2 × (SWB run mean green − R) recovers the global change in both worlds (W17 RMP 4.20 vs 4.44; AH 0.61 vs 0.66). So in W17 part of the response depends on the network-wide share of gliding vehicles and is shared by treated and control windows: γ ≈ 1.0 s for RMP, 0.4 s for AH; ≈ 0 on grid4.
- **Two-share (saturation) extrapolation** on W22-B (grid4): T̂₁ − Ĉ₀ from MIX at (0.3, 0.7) gives RMP 14.51 vs GTE 14.05 (naive 12.07), AH 1.38 vs 1.57 (naive 2.81), RWV −1.00 vs −0.96.
- **Control spillover** C_p − R has the sign of the human drivers' global change H (SV − R) in 5 of 6 family-world cells; grid4 RWV is the exception, and small.
- **Day-level randomisation** from SV / R rows (unpaired days) is unbiased. Days needed for 80 % power per unit: RMP < 1, AH median 2–4, RWV 8–10. Simulated days differ only by seed.

**Predictions (registered now):**
- **E1:** the two-share extrapolation from MIX at p 0.3 and 0.7 recovers GTE (bias interval contains 0) for SRL and RDQ on grid4 and for RMP, AH and RWV in W17. Pair (0.5, 0.7) is descriptive.
- **E2:** the naive per-vehicle A/B test (p 0.5) overstates the harm (bias interval > 0) for SRL and RDQ. Both have H < 0 (humans gain, −0.61 / −1.21) and count waiting or halted vehicles like AH.
- **E3:** in W17 the network-wide switchback (NSW, 600 s, p 0.5) gives a network green contrast for RMP and AH that is larger than the per-signal τ and whose interval contains the global change. The contrast is network-mean green in treated minus control windows (greens ≥ 60 s into a window, window-weighted).
- **E4 (descriptive):** control spillover sign = sign(H) for SRL and RDQ.

**Runs:**
- grid4 MIX p 0.3 / 0.5 / 0.7 for SRL (t84–88) and RDQ (t89–93); fleets s1413, s1513; days 1400–1409.
- W17 MIX p 0.3 / 0.7 for RMP, AH and RWV (p 0.5 exists, W22-C); fleets s2213, s2313; days 1420–1429.
- W17 NSW for the same three families.
- 150 jobs.

**Checks:**
- KW22-0 (grid4) and KW22-C1 / C2 (W17) with the current wrapper;
- KW17-0 lines.

## Result note W22-E (17/10/2026 17:50; ledger C-261)

- **E1 held 5 / 5.**
- **E2:** held for RDQ; failed for SRL (+0.49 [−0.04, +1.03]).
- **E3:** held for RMP. For AH the criterion was met but the interval is uninformative.
- **E4:** held for SRL and RDQ.
- The two shares were run on the same simulated days.

## Correction to the W22-E reading (18/10/2026 07:37; ledger C-263), found before any new run

The W22-E post-hoc reading "W17 has a network-share component γ ≈ 1.0 / 0.4 s that grid4 lacks" compared the switchback's per-signal late-green window-weighted τ with the truth's pooled all-green metric. With one metric throughout:
- (SWB treated − R) + (SWB control − R) reproduces SV − R in all six cells.
- γ is present in both worlds: MPLight 0.50 (grid4) / 0.78 s (W17); AH 0.26 / 0.18 s.
- The W17 shortfall of the registered τ is mostly that estimator. Its burn-in removes long greens just after a switch into a treated window.

E3's result stands as registered: the NSW green contrast recovered MPLight's change. Its motivation is restated: NSW captures γ in either world.

## Amendment W22-F (18/10/2026 07:38, before any W22-F run): four follow-ups

**User (18/10):** "làm 1234, 4 làm trên mạng lớn hơn đi". The four follow-ups:
1. a same-day two-share design;
2. the sign rule and the two-share extrapolation on the other W19 families;
3. a direct probe of the mechanism;
4. area randomisation on a larger network.

The only substantially larger network with trained families, fleets and a service is the full Midtown map (511 learned signals; MT-E setting as in W21-B). spider (18) and rand3 (21) are barely larger than grid4.

**Battery guard and identity checks:**
- The battery guard is as before.
- The edited wrapper must reproduce SV / R and W22's MIX row on grid4 (KW22-0) and SV / R in W17 (KW22-C).
- On Midtown, the all / none truth runs must reproduce W21-B's MTW_SV / MTW_R rows bit for bit on the row fields (KW22-F4).

### F1: the same-day two-share design (S2D), grid4 RMP / AH / RWV / SRL / RDQ and W17 RMP / AH / RWV; fleets as W22-B / W22-C; 10 days
- **Assignment:** a fleet vehicle departing before 1800 s uses SPaT with probability p_a, one departing later with probability p_b. (p_a, p_b) = (0.3, 0.7) on even days and (0.7, 0.3) on odd days (5 / 5). Wrapper kind `vt`; vehicle hash as MIX.
- **Measured trips:**
  - departures in [900, 1800) for the first share;
  - departures in [2700, 3600) for the second share.
  - The 900 s after the start and after the switch are burn-in.
- **Estimator:** per day the two-share formula (0.3, 0.7) on the treated / control fleet means of the two measured windows, averaged over days.
- **Truth:** SV − R agent time loss over the same two departure windows, from the rows' 900-s window sums.
- **Predictions:**
  - **F1a:** bias interval contains 0 in every cell.
  - **F1b:** the error sd over random half-splits of the days is below the unpaired emulation's (C-262: 0.79–1.05 s/veh per unit). Computed as the unit-level sd of the 10-day mean (per-day sd / √10), against C-262's sd for the 5 + 5-day unpaired design.

### F2: the other W19 families (grid4; B1H, B2H, AD, B1D, B2D, S05, S2, R1, R100; t39–t83, 5 lights each); fleets s1413, s1513; days 1400–1409
- **Arms:** MIX at p 0.3 / 0.5 / 0.7.
- **H (humans' SV − R) from existing rows:** B1H −0.12, B2H −0.31, AD −0.84, B1D −0.06, B2D −0.06, S05 −1.18, S2 −1.17, R1 −1.23, R100 −1.11.
- **Predictions:**
  - **F2a (sign):** naive A/B bias (p 0.5) > 0, interval excluding 0, for AD, S05, S2, R1 and R100 (|H| ≥ 0.8). No bias shown for B1H, B1D and B2D (|H| < 0.15). No prediction for B2H.
  - **F2b (size):** for the five strong families, bias / (−H) lies in [0.5, 3.0]. Observed so far 0.75–2.9.
  - **F2c:** two-share (0.3, 0.7) bias interval contains 0 for all nine.
  - **F2d:** control spillover C(p) − R has the sign of H at p 0.5 and 0.7 for the five strong families.

### F3: the mechanism behind γ and the W17 switch transient (grid4 and W17; RMP and AH; fleets as above; 4 days)
- **Arms:** SWB (300 s, p 0.5), all, and none, each with an extended read-only probe (`W22_PROBE=2`):
  - greens per (signal, window, 60-s offset bin);
  - every approach passage (vehicle × signal) with: halted on the approach (speed < 0.1), the signal's window assignment at entry, the upstream signal's assignment at entry (−1 if none), and the vehicle class;
  - vehicles in the network per window.
- **Predictions:**
  - **F3a (transient):** in W17 MPLight, greens starting in the first 60 s of a treated window are longer than the treated window's later greens. That excess exceeds grid4's.
  - **F3b (mechanism of γ):** in SWB control windows, the halting share of fleet and human vehicles approaching a signal is below the none run's at the same signals, for MPLight in both worlds. The reduction is larger when the upstream signal was treated at entry than when it was not.
  - **F3c (descriptive):** vehicles in the network: SWB lies between none and all.

### F4: area randomisation on the full Midtown map (MT-E setting; families AH t34–38, the threshold loop present per W21-K; and B2D t59–63, no stop-thresholded input); fleets s1413, s1513; days 0–4
- **Arms:** all, none (truth and the identity check KW22-F4), AREA, and MIX p 0.5.
  - AREA (`area:4:2`): the 511 + 56 signals are split into four strips of equal count along their principal axis, i.e. Manhattan's length. Each day two strips are treated, chosen by hash, and fleet vehicles use the SPaT of signals in treated strips only.
- **Outcome:** per-approach-passage delay of fleet vehicles: time-loss seconds on a signal's controlled incoming lanes per passage, by signal (probe `W22_PROBE=3`).
- **Truth:** all − none per passage, averaged over signals.
- **Estimators:**
  - AREA: two-way fixed effects (strip, day) on strip-day mean per-passage delay, with a treated indicator, and a buffered variant excluding signals in the outer 10 % of each strip along the axis (descriptive);
  - MIX: treated − control fleet vehicles' per-passage delay.
- **Predictions:**
  - **F4a:** MIX bias interval excludes 0 for AH, and contains 0 for B2D, whose Midtown cost is the GLOSA rule's own (W21-L0).
  - **F4b:** the AREA bias interval contains 0 for both families, and |AREA bias| < |MIX bias| for AH.

**Size:**
- F1 80 jobs × 10 days;
- F2 270 × 10;
- F3 120 × 4;
- F4 80 Midtown jobs × 5 days.

About 3 h with 9 lanes on AC power. Smoke first, for every kind.

## Result note W22-F (18/10/2026 11:57; ledger C-264, audit C-265)

- **F1:** F1a held 8 / 8 (S2D bias intervals all contain 0). F1b failed 8 / 8 (unit sd 0.96–1.53 against the unpaired 0.79–1.05).
- **F2:** F2a held 8 / 8, F2b 5 / 5 (bias / (−H) 1.08–1.38), F2c 9 / 9, F2d 5 / 5.
- **F3:** F3a held. F3b failed: MPLight's control-window halting equals the none run's. F3c (descriptive): none < SWB < all in all four cells.
- **F4:** F4a held 2 / 2. F4b held for AH and failed for B2D (+0.11 [+0.00, +0.22]).
- **Audit (post hoc, C-265):**
  - KW22-F2: 18 / 18 identical, so the W19 truth rows of the F2 families are reproduced by the W22-F chain.
  - F1b's failure is not an artefact of the order term or of the windowed truth.
  - The F4 unit bootstrap omits the shared daily strip draw. The design sd of the AREA cell mean is 0.12–0.23 s per passage, so neither F4b verdict is informative at 4 strips × 5 days.
