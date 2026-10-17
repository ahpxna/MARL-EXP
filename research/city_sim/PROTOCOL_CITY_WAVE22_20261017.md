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
