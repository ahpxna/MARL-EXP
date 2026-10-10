# PROTOCOL N2M: why does the state forecast cost agent time? (registered 05/10 ~00:37, before any run)

**Trigger:** N2 (C-99) gives the frozen fleet −3.3 % agent fuel vs R, but agent TL rises +2.1…+2.3 s/veh while human TL falls −1.2. Under SPaT:
- mean halting falls 2.93 → 1.6;
- the mean green rises 14.8 → 16.9 s.

The same pattern appears, smaller, with c2.

**Hypotheses (sub-hypotheses of N3, publication feedback):**
- **M-HD (hidden demand):** eco-approaching fleet vehicles move above 0.1 m/s, so the frozen RL-H does not count them as halting (its input and its training reward). It therefore holds the other direction's green longer, and agents wait.
- **M-FB (feedback vs intrinsic):** the time cost needs the light to react to the fleet. With the light schedule held fixed (open loop), it disappears.

## Design (DEV 600–611; RL-H k0 / k1 × R10 L11_s13 / s113; crossed bootstrap light × fleet × traffic as in N1 / N2)

**M-HD.** An input adapter in front of the FROZEN light (existing E4 option `--light-obs q:A:B`): halting + A·count(0.1 ≤ v < 2) + B·count(2 ≤ v < 5) on the same served lanes. Light weights are unchanged.
- Arms:
  - `Rq10` / `Rq11`: σ\* fleet (no SPaT) + adapter q:1:0 / q:1:1 — the adapter's own effect;
  - `N2q10` / `N2q11`: N2 q0.5 + adapter.
- Rights: this changes the light's INPUT (an infrastructure-side sensor definition, speed bins on the served lanes). It is a different right from the SPaT service and is reported as such.

**M-FB.** Record R's phase trace per (k, seed) (fleet σ\*), then replay it (all lights forced) with:
- σ\* (`RPsig`; check KM-2);
- N2 q0.5 (`RPn2`);
- c2 q0.1 (`RPc2`).

## Checks

- **KM-1:** the recording runs reproduce R's rows (all endpoint fields equal).
- **KM-2:** σ\* under replay reproduces R's rows (all endpoint fields equal; the same check as M3′-D KD-3).
- **Smoke:** each script type runs on seed 600 before the panel.

## Decisions (registered)

**M-HD SUPPORTED** iff, for some adapter AB:
- N2qAB − N2q05 has agent TL upper < 0, with point ≤ −0.5;
- and N2qAB vs RqAB still saves fuel (point ≤ −2 %).

**CANDIDATE (M3 limits, vs the registered R)** iff N2qAB vs R has:
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports ≤ R + 0.1 and unfinished ≤ R.

A candidate here is a DEV candidate only. It is frozen, then confirmed on 700–739 with new lights / fleets, and must beat the same-rights comparators: adapter alone, N2 alone, c2 + adapter.

**M-FB:**
- FEEDBACK-DOMINANT iff open-loop RPn2 − RPsig agent TL upper < +0.5 while closed-loop N2q05 − R agent TL lower > +1.0;
- FLEET-INTRINSIC iff open-loop RPn2 − RPsig agent TL lower > +1.0;
- otherwise MIXED.

**Scope:** two adapters (no tuning), one q (0.5), one forecaster (N2 as fitted in job 030).

## Amendment X3 (00:45, after the N2M report; registered before the run)

M-FB came out FLEET-INTRINSIC: in open loop, N2 costs +2.72 s/veh agent TL with no fuel gain. Is that a forecast error, or the frozen fleet's own time-for-fuel trade-off under RL-H's short greens?
- **Test:** the same recordings, replayed with the EXACT future (the C-61 oracle `CITY_m3_headroom.py`; a diagnostic, not deployable). Arm `RPex`, k0 / k1 × s13 / s113, DEV 600–611.
- **Decision (`scripts/CITY_x3_report.py`):** EXACT ALSO COSTS AGENT TIME iff RPex − RPsig agent TL lower bound > +0.5. Otherwise INFO-LIMITED.
