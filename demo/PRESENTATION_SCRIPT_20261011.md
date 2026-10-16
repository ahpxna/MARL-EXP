# When AIs Meet AIs — presentation script (11/10/2026, final)

Demo: `demo/gridlock_to_green.html` (or http://localhost:8790/gridlock_to_green.html). Tabs: **Midtown Manhattan** → **Two AIs meet** → **Test grid**. Default speed 4×.

**One-line thesis:** *We trained two AIs on a 16-signal toy city, made them work together, and dropped them — unchanged — into the full street map of Midtown Manhattan. They beat the city-style actuated signals by 21% on delay and 11% on fuel.*

---

## The talk (~3 minutes + demo)

### 1. Hook (15 s)
> "Every company is shipping AI. Soon, most of what your AI sees won't be people — it will be other AIs, built by other teams and trained on their own. Traffic is where that happens first: AI traffic lights, and AI cars that drive themselves to save fuel. We asked a simple question: **what happens when two independently trained AIs meet in a real city — and how do you make them work together without retraining either one?**"

### 2. The first surprise: two good AIs can be bad together (40 s) — *tab "Two AIs meet"*
> "We built both. An AI traffic signal, and a fleet of AI eco-driving cars that know when the light will turn and glide in instead of stopping.
> Each one is good alone. Put them together and the AI cars get **worse**.
> Why? The standard way to build an AI signal — the default in sumo-rl and in the RESCO benchmark — describes traffic by the cars that are **stopped**. A gliding AI car barely counts. So the signal serves it last.
> This chart shows the damage on five standard signal designs: up to **16 extra seconds** per AI-car trip.
> Our fix is a thin translation layer we call **TSI-G**: the signal sees each AI car as the human driver it replaced. **No retraining of either AI.** The extra delay goes from +5.4 to −0.2 seconds on sumo-rl's design, 97% of it disappears on MPLight's, and the AI cars burn 5–10% less fuel."

*(point at the chart: open circles = without TSI-G, filled = with; the 'wave' row is the control — it counts every car, so there was nothing to fix)*

### 3. The real test: Manhattan (60 s) — *tab "Midtown Manhattan", default comparison*
> "Then we took both AIs — trained only on a 16-signal toy grid — and dropped them into the **full street map of Midtown Manhattan**, river to river: 567 signals, 206 kilometres of road. No retraining.
> The first time, the whole city **gridlocked**. It looked like the AI had failed.
> It hadn't. We traced every stuck car back to where its jam began. The jams didn't start at the AI signals — they started at the 56 complex junctions the AI can't run: tunnel ramps, bridge approaches, a seven-phase intersection on 57th Street. Those were left on fixed timing, and fixed timing can't cope — fixed timing everywhere gridlocks too.
> So we deployed it the way a city would: **the AI runs the 511 simple intersections, the city's own actuated controllers keep the 56 complex ones.**
> Result, against actuated signals everywhere, over 100 test runs: **21% less delay, 38% less time stopped, 11% less fuel. The AI won 98 of 100 runs on delay, and all 100 on fuel.**"

*(press **Zoom in**: queues on the left, traffic rolling on the right)*

### 4. What makes it interesting (30 s)
> "Three things surprised us.
> **One — small beats big.** Retraining the signals on Manhattan did not help. Giving every intersection its own extra policy made things worse on new days — it overfit. The policy learned once on a tiny grid generalised best: all five independently trained models beat the city's controller.
> **Two — two AIs beat one.** With the AI cars on top of the AI signals, fuel drops another 3%, and our best pair finished five rush hours with **zero** stuck cars.
> **Three — the failure wasn't the AI.** The headline result only exists because we diagnosed where the jam started instead of blaming the model."

### 5. Why it matters (15 s)
> "The pattern is general: when AIs from different teams meet, don't retrain everyone — **fix the interface between them**, and deploy them where their assumptions hold. That's a compatibility layer for AI, and we showed it works on a real city map."

### Closing line
> "Two AIs, trained on a toy town, no retraining — and Midtown moves 21% faster."

*(optional: "How they learned" button — the signals and cars learning at 20× on the grid)*

---

## Highlights to show off (numbers to say out loud)

| Claim | Number | Evidence |
|---|---|---|
| Real map scale | 567 signals, 206 km, river to river (about 19th–74th St) | `research/city_sim/net/midtown_full.net.xml`; OSM via Overpass 11/10 |
| AI lights + AI cars vs actuated | **−21% delay** (162 → 127 s), **−38% stopped** (71 → 44 s), **−11% fuel** (328 → 291 g) | 100 runs = 5 test days × 5 signal models × 4 fleets; paired: delay −34.5 s [−36.2, −32.5], better in 98/100; fuel better in 100/100 |
| AI lights alone vs actuated | −20% delay, −25% stopped, −8% fuel; 24/25 runs better | 25 runs |
| Best pair | signal model **t63 + fleet s1413**: **−25% delay**, −12% fuel, **0 stuck cars in 5 days** | `eval_full/MTF_BGar_t63_s1413.json` |
| Worst pair still wins | t61 + s1713: 139 s vs 162 s actuated | same panel |
| Two AIs > one | AI cars save another **9.7 g/trip** (−3%) on top of AI lights, interval [−10.9, −8.6] | paired by light and day, 100 pairs |
| Naive deployment fails | 421 s with the 56 complex junctions on fixed timing; fixed timing everywhere 644 s | MT-C |
| Where the jam starts | 7-phase signal on E 57th St, 6-phase in the 1st Ave Tunnel, a fixed 4-phase signal on 2nd Ave | teleport log, `diag_maxg/tele_full_LG59_d0.json` |
| Two-AI mismatch (paper result) | extra AI-car delay up to **+16 s/trip**; TSI-G: sumo-rl +5.4 → −0.2 s, MPLight +16.0 → +0.5 s (97% removed), RESCO IDQN +2.6 → −0.2 s; AI-car fuel −5 to −10% | grid panel: 20 days × 5 signals × 4 fleets |
| Test grid | −71% delay, −93% stopped, −26% fuel vs fixed timing | grid panel |
| Small beats big | Manhattan-retrained signals no better (−5.6 s, not significant, old map; +28 s on the full map with the complex junctions on fixed plans, where both gridlocked); per-intersection gated policies +32 to +115 s (overfit); forecast re-fitted on Manhattan +40 s (one model learned from jammed data) | MT-A3/A5, MT-F |

---

## Demo click path (2 minutes)
1. Open the page. The **Midtown Manhattan** tab is already on "Actuated signals → AI signals + AI cars". Let it play at 4×. Point at the "cars stopped now" counters, left vs right.
2. Press **Zoom in**: the same 650 m corner of both maps, so queues and gliding cars are visible.
3. Scroll to the cards (−21% / −38% / −11%) and the dot chart (every dot is one run; the AI rows sit left of actuated).
4. Switch the dropdown to "Actuated → AI signals (human drivers)" to show the signals alone (−20%).
5. Tab **Two AIs meet**: left = without TSI-G (the AI cars wait), right = with TSI-G. Then the chart of five signal designs.
6. Optional: **How they learned** (corner window, 20×).

---

## If asked — honest facts (do not volunteer)

**Simulation and baseline**
- Everything is SUMO simulation. Demand is random trips at 4 800 per hour, not NYC counts.
- The baseline is SUMO's actuated controller, **not** NYC's live Midtown in Motion system.
- Fuel uses the HBEFA4 model.

**Deployment setup**
- "Stuck cars" means SUMO removed a car after it waited 300 s (a teleport).
- The AI controls only two-phase intersections (511 of 567). The other 56 keep the actuated program, which the baseline also uses, so the difference comes entirely from the 511.

**Manhattan details**
- Clips: test day 0 is the median day of the actuated baseline (rule fixed in advance); signal model t59, fleet s1413.
- The SPaT forecast the cars use was learned on the grid and adapted to Manhattan with no per-light identity.
- We also re-fitted the forecast on Manhattan traffic (MT-F, interface only, 100 paired runs). It did **not** help: +40 s delay.
  - All of the loss comes from one signal model, whose training data was collected in jammed traffic, so its forecaster learned the jam.
  - On the other four, it saved about 1% fuel with no change in delay.
- An earlier demo used a partial OSM extract (248 signals); the full-map results replace it.

**TSI-G**
- On MPLight's representation, the last 0.5 s missed our pre-registered limit, so call it "97% removed".
- The older TSI version's −3.85% fuel holds with the HBEFA fuel model, reverses with PHEMlight, and fails when every driver uses IDM instead of Krauss.

**Generality**
- The other domains are analogies; only traffic was tested.

**AWS (idea, not built)**
- Models in SageMaker.
- The translation layer as a Lambda between two vendors' systems.
- A CloudWatch alarm when a partner's behaviour leaves the training range.

---

## Screen-recording plan (clock = the simulation clock under the map; at 4×, 1 sim-minute = 15 s of video)
Browser wide enough for the two maps side by side; speed 4×; jump with the scrub bar.

| Shot | Tab / comparison | Record (sim clock) | Watch for |
|---|---|---|---|
| A. Gridlock | Midtown, "Fixed-time → AI signals + AI cars" | 26:20 → 27:20 (15 s) | left: ~600 cars stopped, 11 km/h; right: ~55, 34 km/h. Fixed timing, not the AI |
| B. Main result | Midtown, "Actuated → AI signals + AI cars" | 25:00 → 28:50 (58 s); **Zoom in** at 25:30, out at 27:10 | stopped now 97 vs 61 (25:30), 86 vs 53 (26:30); stopped so far 91 vs 60 car-min at 26:00, 261 vs 176 at 28:00. **Stop before 29:00** (right side spikes to ~83) |
| C. Proof | same, scroll down | still, 8 s | cards −21% / −38% / −11%; dot chart, AI rows left of actuated |
| D. Signals alone (optional) | Midtown, "Actuated → AI signals (human drivers)" | 25:00 → 26:00 (15 s) | 97 vs 66 stopped at 25:30 |
| E. Two AIs meet | "Two AIs meet", MPLight comparison, Zoom in | 25:00 → 28:00 (45 s) | AI cars stopped so far: 2.3 vs 0.5 at 26:00, 5.7 vs 1.2 at 28:00; then the five-design chart (8 s) |
| F. Toy grid (optional) | Test grid | 26:00 → 27:00 (15 s) | 24–34 vs 2 stopped; then "How they learned" 10 s |
