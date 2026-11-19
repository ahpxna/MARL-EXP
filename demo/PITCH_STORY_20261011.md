# When AIs Meet AIs — hackathon story (11/10/2026, v2: matches the demo page)

The story: **improve a system that already works fairly well, then fix what happens when two AIs meet.**
The traffic city is the test case. The problem it shows is one every company shipping AI will hit: **one team upgrades its AI, and another team's AI silently gets worse.**

Page: `demo/gridlock_to_green.html` (title "When AIs meet AIs"). Tabs in this order: Midtown Manhattan → Two AIs meet → Test grid.

---

## The 2-minute pitch (English, to read aloud)

**1. Hook (15 s)**
"Every company is shipping AI. Soon, much of what your AI sees will not be people. It will be other AIs, built by other teams and trained on their own. Nobody tests what happens when they meet."

**2. First, AIs that transfer (30 s)** (tab *Midtown Manhattan*, default "Actuated signals → AI signals + AI cars")
"This is the full street map of Midtown Manhattan, river to river: 567 signals and 206 kilometres of road. Our AIs never saw this city. They learned on a small grid of 16 signals.
- Left: actuated signals, the reactive kind that hold green while cars are detected.
- Right: our AI signals at every two-phase intersection, and half the cars are AI eco-drivers that know when each light will turn. Same streets, same day.

Over 100 test runs (five test days, five signal models, four car fleets), delay per trip drops 21 percent, time stopped drops 37 percent, and fuel drops 11 percent. The AI wins on 98 of the 100." *(press Zoom in: queues on the left, rolling traffic on the right)*

**3. Then the problem nobody tests (30 s)** (tab *Two AIs meet*)
"Now add a second AI: a fleet of eco-driving cars that knows when lights will change and glides instead of stopping. Each AI is good on its own. Together, something breaks.
- The standard way to build an AI traffic signal describes traffic by the cars that are *queued*: stopped.
- A gliding AI car barely registers. The signal under-serves it, and the AI cars wait longer.

With the default state of sumo-rl, the most popular open-source framework, that is 5 extra seconds per trip. With RESCO MPLight's representation, it is 16. Nothing crashes; it just quietly gets worse."

**4. The fix (30 s)** (*point at the right panel, then the chart*)
"Our fix is a thin compatibility layer called TSI-G, and we retrained neither AI.
- The signal now sees each AI car as the human driver it replaced, through a calibrated twin.
- The cars keep their signal forecast.

The extra delay goes from plus 5.4 to minus 0.2 seconds. Across the standard signal designs it removes 97 to 100 percent of the harm, and AI-car fuel is 5 to 10 percent lower than without the forecast. The fifth row, the wave state, counts every car, so it never broke; that is our control."

**5. Why it matters beyond traffic (15 s)**
"The recipe is general: translate your partner into the inputs your model was trained on. The same gap appears wherever a model was tuned on human behaviour and now faces AIs: fraud models meeting AI shopping agents, recommenders meeting AI-generated content, warehouse schedulers meeting new robot fleets. The product is **compatibility testing for AI upgrades**: before you ship v2, replay it against your partners' frozen models in a simulator, and if it breaks them, generate the adapter."

**Closing line**
"We don't need to retrain every AI each time someone else's gets smarter. We need a compatibility layer, and we built one that works on a city."

*(Optional, if there is time: the **How they learned** button shows the signals and cars learning at 20× on the grid.)*

---

## One-liners
- "Your upgrade just broke my AI, and neither of us got an error message."
- "Smart alone, worse together, fixed without retraining."

## If someone asks: facts to keep in mind (do not volunteer)

**Midtown, full map (Overpass 11/10: 567 signals, 206 km)**
- AI signals + AI cars, against actuated, 100 runs: −21 % delay, −37 % stopped time, −11 % fuel. Better in 98, 98 and 100 of 100 runs.
- AI signals alone: −20 % / −25 % / −8 % (25 runs).
- The AI cars add about 10 g of fuel saved per trip (−3 %) on top of the AI signals.
- **Setup:** the AI runs the 511 two-phase intersections. The 56 complex junctions (3- to 7-phase: tunnel and bridge approaches, 57th St) keep the city's actuated programs, which is how a city would deploy it.
- **If those 56 are left on fixed-time plans, the network gridlocks** (421 s with AI, 644 s with fixed-time everywhere). The jam starts at those junctions, not at the AI lights.
- A 50 s maximum green does not fix that.
- SUMO simulation with random trips at 4 800 per hour. The baseline is SUMO's actuated controller, not NYC's live system (Midtown in Motion).
- An earlier version of this demo used a partial map (248 signals, about 29th–61st St). That map is superseded.

**What did not work (be honest if pushed)**
- Retraining the signals on Manhattan did not beat the transferred grid models.
- One extra per-intersection policy with a learned gate overfits: +32 to +115 s on new days.
- A model fine-tuned on the partial map did worse on the full map (+28 s).

**The fix (TSI-G)**
- Grid panel: 20 traffic days × 5 signal models × 4 AI fleets.
- On MPLight the remaining 0.5 s misses the pre-registered limit (upper bound 0.74 s), so call it a large partial repair.
- Human drivers lose 0.5 s per trip with TSI-G compared with the broken setup, which had favoured them.
- The −3.85 % fuel result of the earlier TSI version holds with the HBEFA fuel model, reverses with PHEMlight, and fails when every driver uses IDM instead of Krauss.

**Scope**
- The other domains are analogies. Only traffic was tested.

**AWS mapping (idea, not built)**
- Models in SageMaker.
- The adapter as a Lambda at the boundary between two vendors' systems.
- A CloudWatch alarm when a partner's behaviour leaves the training range.
