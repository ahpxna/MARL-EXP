# PROTOCOL N4: selective SPaT provision with the N2 forecaster (registered 05/10 ~00:41, before any gated run)

**Hypothesis N4** (`METHOD_HYPOTHESES_NIGHT_20261004` §2–3): a service layer chooses, per query, between the forecast and `unavailable` (the fleet then drives σ\*). It keeps more benefit than publish-all.

**Motivation:**
- N2 publish-all gives −3.3 % agent fuel vs R, but +2.1…+2.3 s/veh agent TL (C-99).
- The suspected mechanism is long red-wait slowdowns that hide demand from the light (N2M is being tested).
- Light and fleet weights stay frozen; only the information service changes.

## Gate (causal; `scripts/CITY_spat_forecast_n4.py`)

Inputs at the query second:
- w = pred(q0.5) − pred(q0.1) of the answered event (interval width);
- the answered horizon (ttg of a link waiting for green);
- a deterministic hash for the random arm.

Families:

| Spec | Rule |
|---|---|
| `all` | publish always (= N2 at q0.5) |
| `w:τ` | publish iff w ≤ τ (confidence-only) |
| `h:τ` | publish iff the link is green now or its ttg ≤ τ (horizon) |
| `wh:τw,τh` | both conditions |
| `rnd:p` | publish with probability p (matched activation) |

**Not tested here:** a receiver-aware feature (command variation of the frozen fleet across the plausible TTG range). The provider interface is per (light, link). The gate is therefore the A-no-receiver form; a receiver-aware gate is a follow-up only if a simple gate works.

**Check KN4-1:** `all` reproduces the N2 q0.5 rows on smoke seed 600 (all endpoint fields equal).

## Selection (SELECT seeds 650–655: generated fresh after a non-existence check; never used for anything else)

- Grid (16): `all`; `w` ∈ {3, 6, 10}; `h` ∈ {10, 20, 30}; `wh` ∈ {3, 6, 10} × {10, 20, 30}.
- Run on RL-H k0 / k1 × fleet s13 × 6 SELECT seeds, against R on the same seeds.
- J = agent fuel % vs R + 5 · Σ max(0, ΔTL) over city / agent / human TL, pooled over k.
- Registered choices:
  - G\* = argmin J over the grid;
  - Wbest = argmin over the `w` family;
  - Hbest = argmin over the `h` family;
  - RND = `rnd:p` with p = G\*'s SELECT activation.
- Budget: 34 jobs × 6 seeds.

## DEV screening (600–611; RL-H k0 / k1 × fleets s13 / s113; crossed bootstrap)

- Arms: G\*, Wbest, Hbest, RND(p).
- Existing rows: N2 publish-all (n2_20261005/dev N2q05) and R (n1_20261005/g4).

## Decisions (registered)

- **N4 CANDIDATE:** G\* vs R meets every M3 limit:
  - agent fuel upper < 0;
  - city / agent / human TL upper < +0.5;
  - teleports ≤ R + 0.1.
  - A candidate is a DEV result: freeze, then confirm on 700–739 with new lights / fleets, against publish-all, confidence-only, horizon-only and random.
- **N4 SUPPORTED (selection helps):** both of:
  - G\* − publish-all (paired) has agent TL upper < 0 with point ≤ −0.5, and agent fuel point ≤ +1.0;
  - G\* − RND(p) has agent fuel upper < 0 or agent TL upper < 0.
- If Wbest or Hbest alone matches G\* (paired difference CI includes 0), the simplest family is the reading. No receiver-specific claim is made either way.

## Amendment A1 (00:46, before the N4 DEV panel was read; SELECT still running)

**Registered follow-up arm GQ:** the SELECT-chosen gate G\* plus the light-input adapter q:1:0. N2M showed that q:1:0 alone cuts N2's agent TL by 0.8 s (C-100); the two levers are not assumed additive (C-101).

- Arms: GQ on DEV 600–611 × k0 / k1 × s13 / s113, with comparators G\* (N4), N2 + q:1:0 (N2M) and R.
- Rights: SPaT service plus a light-input sensor definition (light weights frozen).
- **Decision:** GQ CANDIDATE iff GQ vs R meets every M3 limit (as in N4). A candidate is frozen and confirmed as stated in N4.
- Job `036_GQ_gate_adapter.sh` runs after 033 / 034; it reads `sel/choice.json`.

## Amendment A2 (00:52; registered before the run)

**Arms HYB and HYBQ (C-102, X2).**
- HYB = N2 q0.5, except that while a light shows a yellow, the answer comes from provider c2 on the k-specific table. c2 is exact there; N2 has a 0.7–5.4 s error in those cells.
- HYBQ = HYB + the light adapter q:1:0.
- Same DEV cube as N4.
- **Decisions:**
  - HYB − N2q05 (paired) is reported; "the hybrid fix helps" iff agent TL upper < 0 or agent fuel upper < 0, the other not worse by > +0.5;
  - CANDIDATE iff HYB or HYBQ vs R meets every M3 limit.
- Engineering correction; no novelty claim.

**Provenance note:**
- `CITY_spat_forecast_n4.py` was edited at 00:51 while job 033's DEV panel was launching new processes.
- The edit only adds the `hyb` branch and a `hybrid` counter in the sidecar. The arms all / w / h / wh / rnd follow identical code paths.
- Recorded in C-103.
