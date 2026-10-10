# PROTOCOL — M2: does upgrading the light to a learned controller lose the confirmed fleet's benefit? (04/10/2026 16:32; registered before any M2 run)

Milestone M2 of `TWO_POPULATION_PAPER_FINISH_LINE_20261004.md`; opened after M1 was met by R9 (C-54) and R10 (C-57), as step 4 of the R8–R10 progress audit. Evaluation only: no training and no re-fitting.

## Populations (all frozen)

**Lights:**
- **L0 = FT.** The grid4 static programs, 90 s cycle. This is the light both fleets were fitted or trained under.
- **L1 = RL-H:k**, k = 0..3. The learned light (four training seeds), trained on grid4 with SUMO cars (Q7 / Q7b checkpoints, used in C-30…C-34).
  - It holds each green with `setPhaseDuration(1e5)` and switches through the program's yellow.

**Fleets** (50 % agents, same membership):
- always-SUMO (OFF): σ 0.5, no fleet.
- σ\* = 0.3: SUMO drivers, the strongest non-learned family.
- **F0a = R9:** GLOSA-LD∘σ\*, fitted θ of search seeds 2–5.
- **F0b = R10:** PPO residual on GLOSA-L∘σ\*, seeds 213–513.

## SPaT under L1 (causal labelling, the point of M2)

`CITY_spat_feature.spat` derives SPaT from the light's current STATIC program. Under L1:
- it returns `unavailable` while a green is held (remaining > 1e4);
- during each ~3 s yellow transition, the program looks static, so it returns a **program-derived forecast that L1 does not follow**: the next green's duration is taken from the program (42 s), while L1 holds it for a learned, variable time.

That forecast is therefore mislabelled under L1. Its scope note in the module already excludes "a static program whose phases or durations are changed by a controller".

Two arms under L1:
- **naive:** the fleet uses `spat` as is. This is the realistic deployment mistake.
- **labelled:** L1 declares that it publishes no SPaT. Every `spat` call returns `unavailable`, so the fleet falls back to its base driver σ\*.

Under L0 the two arms are identical (check KM2-1).

## Panel

FRESH traffic **470–489** (20 seeds), generated after this registration with the verified randomTrips config. 300–319 stay reserved.

Pairing:
- Under L1, fleet seed j is paired with light seed k = j (θ_s2 ↔ RL-H:0, …, θ_s5 ↔ RL-H:3; L11_s213 ↔ RL-H:0, …).
- OFF and σ\* run under each RL-H:k.
- Cubes are 4 (pairs) × 20 (traffic), crossed bootstrap, 2 000 draws, one-sided 95 % bounds.
- Under L0, the fleets use their 4 seeds and OFF / σ\* are single rows.

## Endpoints (fuel primary; teleports and unfinished reported)

**M2-A, the light upgrade with SUMO cars (city TL and city fuel).**
- RL-H vs FT, with OFF cars and with σ\* cars.
- Descriptive, plus the sign: the upgrade must be beneficial for the reference population to make M2 meaningful.
- If RL-H is NOT better than FT on city TL (upper < 0), M2 is reported as "the upgrade is not an upgrade in this setting" and the DiD is descriptive only.

**M2-B, fleet benefit under each light**, F0 − σ\* under the same light: agent fuel %, agent TL, human TL. Under L1, for each arm.

**M2-C, the compatibility measure (DiD).**

D = [F0 − σ\*]_{L1} − [F0 − σ\*]_{L0}, on agent fuel %, for each fleet and each L1 arm.

The benefit is "lost" if D's lower bound is > +1 % (the fleet keeps less than its L0 benefit minus 1 point). It is "kept" if the upper bound is < +1 %.

**M2-D, causal-labelling check.** Share of fleet decisions made with `valid` SPaT, and the number of commanded vehicle-seconds, under each light and arm.

**M2-E, harm.** Agent and human TL of F0 vs σ\* under L1 (upper < +0.5 = no harm), for each arm.

## Checks (exit 1)

- **KM2-1:** under FT, naive ≡ labelled for F0a on traffic 0 (bit-identical rows).
- **KM2-2:** under RL-H:0, labelled F0a ≡ the σ\* fleet (eval4_sigma 0.3) on traffic 0, bit-identical. The fleet never commands.
- **KM2-3:** under RL-H:0, the naive arm makes at least one decision with `valid` SPaT on traffic 0. Otherwise the mislabelling concern is void, and that is reported.

## Predictions

| # | Prediction |
|---|---|
| P-M2-1 | RL-H improves city TL over FT with SUMO cars (M2-A). Prior: it improved over ACT by 2.4–2.6 s/veh (C-30 / C-32). FT vs RL-H was not measured. |
| P-M2-2 | Labelled L1: F0a and F0b collapse to σ\* (KM2-2 holds for both), so D ≈ the whole L0 SPaT benefit: about +6.5…+7.6 points of fuel. **The benefit is LOST, without harm** (M2-E passes). |
| P-M2-3 | Naive L1: commands occur only during yellows (M2-D share small, < 10 %), D is also "lost", and the M2-E harm is possible but small (|TL| < 0.5). |

## Reading rule

- If P-M2-2 holds, the compatibility problem in this setting is a **structural loss of the fleet's SPaT benefit** when the light stops publishing a plan. That motivates M3: a learned light that commits its next switch (publishes a guarantee) to keep the old fleet's benefit, at a cost to its own.
- If RL-H is not beneficial (M2-A), the problem is reported as not established for this L1.
- Nothing here claims harm unless M2-E fails.

* Traffic 470–489 generated at 16:32, after registration.
* **Checks (16:34): `m2/check/m2_check.txt` PASS.**
  - KM2-1 bit-identical.
  - KM2-2 bit-identical: labelled F0a ≡ σ\* under RL-H:0.
  - KM2-3: the naive arm sees valid SPaT in 20 223 / 68 707 calls under RL-H:0 (29 %, not only yellows: a new green keeps its program duration until the light's next decision tick). The mislabelling concern is REAL.
  - Traffic-0 smoke, not an endpoint: city TL is about 21 s under RL-H:0 vs about 53 s under FT; naive F0a vs σ\* under RL-H:0 is fuel +7.5 %, agent TL +1.6.
* **The P-M2-3 premise "only during yellows" is already contradicted by KM2-3.** P-M2-3 is evaluated as registered.
* Frozen before the M2 evaluation: CITY_eval6_m2.py d1b00bd0173ddc53; CITY_m2_check.py b37f5c4863ea66dc; CITY_m2_report.py a06cdf591bcd9a1b; RUN_m2_eval.py e128b2e499021b41;

---

## Amendment M2b (16:50): a VALID causal forecast for the learned light (registered before any M2b run; after C-60)

**Why.** The guide requires regression measured with a valid causal SPaT. M2a had only an out-of-scope program-derived arm and a no-SPaT arm (C-60).

**Forecast service for RL-H:k** (one table per light seed k; `scripts/CITY_spat_forecast.py`):
- **Fit** on TRAIN traffic 0–7 only. Phase traces are recorded with `--record` from RL-H:k runs with σ\* cars (the fleet's fallback population).
- **Model:** the empirical distribution of completed green durations G per (intersection, green phase), pooled over the 8 traffic seeds, with the pooled-per-phase distribution as fallback.

**Forecast at time t** uses only the light's current phase and its spent time (causal):
- **In green g with spent s:** the remaining green is the q-quantile of {G − s : G > s}.
  - A link served by g gets ttg 0 and ttr = r_q + 1.
  - A link served by the other green g′ gets ttg = r_q + 3 (yellow) + 1.
- **In yellow:** the remaining yellow time is exact (program timer). The link served by the next green gets ttg = rem + 1. The link served by the green that just ended gets ttg = rem + 1 + q-quantile(G_{g′}) + 3.
- Always-green and never-green links are handled as in `spat`.
- **Label:** `source = 'forecast:q'`, published with its quantiles. It is a forecast, not a plan.

**Arms** (frozen fleets F0a = R9, F0b = R10; a wrapper only, no weights changed):
- **labelled:** no SPaT, as M2a.
- **fc50:** median forecast.
- **fc20:** robust, the 0.2-quantile of the remaining time, i.e. "green may come this early".

**Validation (M2b-1).** Offline, on held-out SELECT 100–104 traces of RL-H:k with σ\* cars.
- For every second and every (intersection, green) not currently green: forecast vs actual time until that green, per movement group.
- Reported: median absolute error, MAE, and coverage of the [q10, q90] interval.
- **Check KM2b-1:** the online forecast function equals the offline computation on a recorded trace (sampled seconds, exact).

**Panel.** NEW traffic **490–509** (20 seeds), generated after this registration. M2a's 470–489 has been seen, and this is a design change after seeing it.

Jobs:
- **FT:** OFF, σ\*, F0a × 4 seeds, F0b × 4 seeds.
- **RL-H:k (k = 0..3), paired with fleet seed k as in M2a:** OFF, σ\*, F0a × {labelled, fc50, fc20}, F0b × {labelled, fc50, fc20}.
- **Commanded vehicle-seconds** are logged for every fleet row (sidecar).

**Endpoints (fuel primary):**

| Endpoint | Content |
|---|---|
| M2b-1 | Forecast validity (above) |
| M2b-2 | F0 − σ\* under RL-H per arm (agent fuel %, agent TL, human TL); DiD vs FT. KEPT if the DiD upper bound < +1; LOST if the lower bound > +1. |
| M2b-3 | Harm: agent or human TL upper bound ≥ +0.5, or fuel lower bound > 0, vs σ\* under RL-H |
| M2b-4 | Commanded vehicle-seconds per arm |
| M2b-5 | System totals (city TL, city fuel) per arm vs OFF and σ\* under RL-H |

**Predictions:**

| # | Prediction |
|---|---|
| P-M2b-1 | Median absolute ttg error ≥ 5 s; [q10, q90] coverage within [0.7, 0.9]. |
| P-M2b-2 | fc50 does NOT keep the benefit (DiD lower > +1) for either fleet. |
| P-M2b-3 | fc20: no harm (M2b-3 passes) and a fuel benefit vs σ\* between 0 and −3 %. |

**Reading rule.**
- If a valid forecast KEEPS the benefit, the forecast is the method baseline M3 must beat, and commitment may be unnecessary.
- If it does not, the remaining gap is what M3 (commitment) must close, at a measured cost to the light.

**Still open after M2b (declared):** a learned L0 (the guide's main experiment) and the adapted-fleet column.
* M2b timeline:
  - Traffic 490–509 generated at 16:51. Traces at 16:51: 4 lights × (TRAIN 0–7 + SELECT 100–104), σ\* cars.
  - Forecast fitted on TRAIN only.
  - **Validation (16:52, `m2b/validation.jsonl`):** median |error| 4 s, MAE 7.9–8.6 s, bias −4.4…−4.9 s, [q10, q90] coverage 0.856–0.857 for all four lights. **P-M2b-1 therefore FAILS** on the error part (the forecast is better than predicted). The forecast is used as fitted, with no bias correction, as registered.
* **Checks (16:55) PASS.**
  - KM2b-0 and KM2b-3 are bit-identical.
  - KM2b-1: 4 112 online reads, 0 mismatches with the recorded trace.
  - KM2b-2: fc50 published 70 536 / 70 536 valid calls; 37 876 commanded vehicle-seconds.
  - Traffic-0 smoke (not an endpoint): fc50 F0a vs σ\* under RL-H:0, fuel +7.98 %, agent TL +3.48, human −1.43.
* Frozen before the M2b panel: CITY_spat_forecast.py f0fe94f9a7e76ae3; CITY_eval6_m2b.py 9dc2b5a400f0ff03; CITY_m2b_check.py 1f7fb42166faea53; CITY_m2b_report.py ab225301a0d22a30; RUN_m2b_eval.py 42a96fbdaa22345f; RUN_traces.sh 238f87db6139a52b;
