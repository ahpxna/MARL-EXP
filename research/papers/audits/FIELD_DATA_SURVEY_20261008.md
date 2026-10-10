# Field-data survey for the TSI paper (08/10/2026, 04:49)

**Request.** User, 08/10: "tìm dữ liệu thực địa đi" (find field data).

**Who did the work.** I searched myself with WebSearch and WebFetch; no subagents were used. Every row below was checked on the source page on 08/10. Nothing has been downloaded yet. Downloads need the user's permission. Free disk is about 10 GiB, below the 15 GiB guard (Docker).

## 0. What field data can and cannot do for this paper

**No public dataset contains a learned signal controller and a learned eco-driving fleet operating together.**
- KI4LSA in Lemgo is the only field deployment of deep-RL signals we know of: about 10% shorter travel times, according to Fraunhofer's press material.
- It published no fleet or SPaT-service data.

**Field data cannot test TSI end to end. It can test the model components on which the claims rest:**

| Component | Paper weakness it addresses |
|---|---|
| Emission model | "fuel claims are claims about two emission models" |
| Car-following model | the IDM failure (W9, W13-6a, W15-3a) |
| Predictability of real adaptive signals; quantile forecast coverage | the forecaster has only been tested in simulation; "transfer from simulated to field logs is untested" |
| Real demand on a real geometry | "synthetic networks only" |

## 1. Sources, by component

### A. Real demand on real intersections (already on disk; GPL-3; no download needed)

**RESCO Salt Lake City scenarios** (`external_assets/RESCO/resco_benchmark/environments/saltlake2_*`):
- **Sites:** two real intersection pairs, "400S & 200W" and "Univ & State".
- **Data:** 365 daily CSVs per signal for 2023, with 5-min counts per movement (12 movements, 288 rows per day). The README states that the scenarios "simulate one year of recorded traffic".
- **Use:** the 2023 days give a natural day-to-day variation, so fresh-day panels can play the role of fresh traffic.
- **Provenance:** the signal IDs (7241/7242, 7142/7243) look like UDOT ATSPM signal IDs. RESCO does not say where the counts came from (not verified).

**Also local:** RESCO `ingolstadt1/7/21`, built from InTAS. InTAS uses signal programs supplied by the City of Ingolstadt and demand validated at 24 measurement points.
- **Caveat:** the earlier attempt on `cologne8` failed at the signal baseline. The grid4 light recipe was worse than fixed time (C-35, C-36). A real network may therefore need a different signal recipe.

### B. Measured fuel near signals (emission-model validation)

**VED, the Vehicle Energy Dataset** (https://github.com/gsoh/VED; Apache-2.0):
- **Fleet and period:** 383 cars in Ann Arbor, Nov 2017 – Nov 2018; about 374,000 miles.
- **Signals:** OBD-II fuel rate, speed, GPS, RPM and engine load.
- **Size:** two 7z files, 82.7 MB and 93.7 MB (176 MB). `bsdtar` (libarchive) can read 7z, so nothing needs installing.

**eVED** (https://github.com/zhangsl2013/eVED; data on Bitbucket; Apache-2.0):
- VED with corrected GPS.
- Adds 195,856 traffic-signal records and 584,551 intersection records matched to trip points.
- Size not stated.

**Possible use:** extract approaches to signalized intersections (glide → stop or slow → re-acceleration). Feed the measured speed traces through HBEFA4 and PHEMlight5 in SUMO, and compare each with the measured fuel. This checks whether the mechanism found in W13 (re-acceleration after glides costs fuel; PHEMlight5 is harsher) matches measured fuel, and which emission model is closer.

### C. Real states of adaptive signals (forecaster and predictability)

**Hamburg traffic-light data, OPARA** (DOI 10.25532/OPARA-466; CC BY 4.0; data © Freie und Hansestadt Hamburg, LSBG, under dl-de/by-2.0):
- **Coverage:** 18,009 signals, 23 Sep – 21 Oct 2023.
- **Content:** primary and secondary signal state changes, cycle second, program, and detector observations (cars, cyclists, pedestrians).
- **Size:** 31.5 GB zipped. **Too large for this disk.**
- **Background:** about 90.7% of Hamburg's signals are adaptive.
- **Published findings** (Jeschor et al., IV 2024, arXiv 2403.18830):
  - 33% of hourly buckets have a cycle discrepancy above 5 s.
  - Only 12% have both a discrepancy above 5 s and a wait-time diversity above 20%.
  - Code: https://github.com/priobike/priobike-predictability-study (MIT).

**Hamburg live SensorThings API** (https://iot.hamburg.de/v1.0; REST and MQTT; same data):
- A few intersections can be pulled for a few days, which would be small.
- **Possible use:**
  1. Fit the TSI forecaster (quantile time-to-switch conditioned on detector state) on real adaptive-signal traces.
  2. Measure the empirical coverage of q0.1 / q0.5, and the cost of early versus late errors.
  3. This is the closest field test of the "publish a low quantile" revision. It is not a closed loop, though: Hamburg's signals do not react to a fleet that uses the forecast.

**Tampa CV Pilot SPaT sample** (data.transportation.gov dataset xn7c-yu2n; CC BY-SA 4.0):
- SAE J2735 SPaT messages from roadside units; small sample in JSON, XML or CSV.
- The full raw data has to be requested from the ITS DataHub Sandbox.
- **Possible use:** see what a deployed RSU actually broadcasts (minEndTime / maxEndTime / likelyTime), against the paper's assumptions about the channel.

**Zurich fully actuated control** (arXiv 2208.11344): an empirical time-to-green study. Whether its data is public is not stated.

**UDOT ATSPM:**
- High-resolution controller event logs with 100 ms events, about 19 MB per signal per day.
- The web site offers visualisations. Public raw download is not documented in the FAQ; UDOT says to contact Mark Taylor. Not verified as downloadable.

### D. Real trajectories at signals (car-following realism: Krauss vs IDM)

**NGSIM Lankershim Blvd (Los Angeles) and Peachtree St (Atlanta)** (data.transportation.gov; public):
- Video-extracted trajectories every 0.1 s on signalized arterials, with signal timing in the supporting data.
- The export can be filtered to one site.

**pNEUMA, Athens** (open-traffic.epfl.ch; CC BY-NC 4.0; terms must be accepted):
- 10 drones, 1.3 km², about 100 intersections, about 0.5 M trajectories at 25 Hz.
- No signal timings ("not available"), and most of the signals are fixed time.

**SinD** (github.com/SOTIF-AVLab/SinD):
- Signalized intersections in four Chinese cities, with traffic-light states and HD maps.
- Access by e-mail request from an educational address.

**Literature, which can be cited without downloading anything:**
- Calibrations of Krauss, IDM and W99 against radar trajectories on a 1.5 km signalized corridor (SUMO 2024; arXiv 2408.03722) and against drone data at a Stuttgart signal (SUMO 2023).
- Reported finding: with default parameters, IDM is closest to the observed accelerations.
- This bears directly on how to weigh the IDM failure: if IDM is the more realistic model, our Krauss-based results are the weaker case.

**Possible use:** calibrate Krauss and IDM to the Lankershim / Peachtree approaches to signals, then re-run the key confirmations under the calibrated model.

### E. Field GLOSA studies (external reference numbers only, no data)

- B-GLOSA for buses (Virginia Smart Road, 30 drivers): 22.1% less fuel and 6.1% less time than uninformed driving.
- A connected-vehicle field study reporting 14% fuel saved.

These are a sanity range for an eco-driving benefit under fixed or predictable signals. They do not involve learned signals.

## 2. Recommended order

| ID | Data | Download | Question | Cost |
|---|---|---|---|---|
| F1 | RESCO Salt Lake (local) | none | Does TSI survive real recorded demand on a real two-signal geometry? | full pipeline: train RL-H and the fleet, M1/M2/TSI. A protocol is needed. |
| F2 | VED (176 MB) | yes | Which emission model matches measured fuel on glide / re-acceleration approaches? Does measured fuel show the W13 mechanism? | analysis only (SUMO emission calls on measured traces); no RL |
| F3 | Hamburg API, a few signals for a few days | yes (small) | Real coverage of the quantile forecaster, and cost asymmetry, on adaptive signals | fit and evaluate the N4 forecaster offline |
| F4 | NGSIM Lankershim / Peachtree | yes | Krauss vs IDM at signals; re-run under the calibrated model | calibration plus the W15 confirmations |

F2 and F3 are cheap and address the two largest reviewer objections: the emission model and simulated forecasts. F1 addresses "synthetic networks", but carries the cologne8 risk. F4 addresses IDM.

## Sources

- VED: https://github.com/gsoh/VED, https://arxiv.org/abs/1905.02081
- eVED: https://github.com/zhangsl2013/eVED, https://arxiv.org/abs/2203.08630
- Hamburg OPARA: https://doi.org/10.25532/OPARA-466; https://opara.zih.tu-dresden.de/items/5ab10b56-679b-4943-8278-dd923427e883/full
- Hamburg study: https://arxiv.org/abs/2403.18830, https://github.com/priobike/priobike-predictability-study
- Hamburg API: https://iot.hamburg.de/v1.0
- Tampa SPaT: https://catalog.data.gov/dataset/tampa-cv-pilot-signal-phasing-and-timing-spat-sample
- Zurich TTG: https://arxiv.org/abs/2208.11344
- UDOT ATSPM: https://udottraffic.utah.gov/atspm/FAQs/Display, https://github.com/udotdevelopment/ATSPM
- InTAS: https://arxiv.org/abs/2011.11995
- NGSIM: https://catalog.data.gov/dataset/next-generation-simulation-ngsim-vehicle-trajectories-and-supporting-data
- pNEUMA: https://open-traffic.epfl.ch/index.php/downloads
- SinD: https://github.com/SOTIF-AVLab/SinD, https://arxiv.org/abs/2209.02297
- Car-following calibration: https://arxiv.org/abs/2408.03722, https://www.tib-op.org/ojs/index.php/scp/article/view/1127
- KI4LSA: https://www.iosb-ina.fraunhofer.de/en/divisions/Machine-Learning/Research-topics-and-projects/Project-KI4LSA-Artificial-intelligence-for-light-signal-systems.html
- B-GLOSA: https://vtechworks.lib.vt.edu/handle/10919/108859
