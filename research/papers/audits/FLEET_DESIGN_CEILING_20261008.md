# Can any fleet design keep a material benefit against realistic drivers? (08/10/2026)

**Question** (user, 08/10): "liệu có thiết kế fleet nào giữ được lợi ích đáng kể so với người lái thật không" (is there any fleet design that keeps a material benefit against real drivers?)

**Basis.** Existing W17 rows only (fresh 1320–1339, FT, the CITY_w13_modes grid) and a literature scan done by me (WebSearch and WebFetch; no subagents). Nothing new was run.

## 1. Where the fuel goes, W17 world (field-matched human drivers, FT, agent subset)

Fuel shares are percentages of the humans' (OFF) agent-subset fuel. "PL − OFF" is the fleet's change in percentage points of OFF fuel. Times are agent hours, OFF → PL.

| Mode | OFF share, HBEFA4 | PL − OFF, HBEFA4 | OFF share, PHEMlight5 | PL − OFF, PHEMlight5 | Time OFF → PL |
|---|---|---|---|---|---|
| idle (v < 0.1, steady) | 17.9% | **−13.70** | 7.9% | **−6.03** | 636 → 149 h |
| creep (steady, 2–5 m/s) | 0.0% | **+12.56** | 0.0% | **+9.22** | 1 → 419 h |
| steady 0.1–2 + 5–10 m/s | 1.0% | +8.56 | 0.8% | +6.26 | 34 → 318 h |
| accel ≥ 10 m/s | 25.7% | −5.74 | 36.1% | −8.26 | 204 → 164 h |
| accel 5–10 m/s | 12.0% | +2.64 | 18.0% | +2.86 | 95 → 151 h |
| **total** | | **−1.08** | | **−0.25** | equal total time |

**Mechanism.**
- The trained fleet avoids stops by creeping behind queues. Creeping costs about as much fuel per second as idling in both emission models, so avoided idling is almost fully paid back.
- The only net gain is smoother high-speed acceleration.
- Against Krauss humans, who brake late and hard, the same fleet gains far more (−8.7%).

**Addressable pool against realistic drivers:**
- idling: 18% (HBEFA4) / 8% (PHEMlight5);
- high-speed acceleration: 26% / 36%.
- A design gains only if it removes idling **without creeping** (arrive when the queue has discharged, from a higher speed), or smooths acceleration without new costs.

## 2. Field and literature evidence (not verified beyond the pages cited)

- **Eco-approach and departure (EAD), field and testbed:**
  - 12.5–15.6% fuel on a Riverside connected-vehicle testbed;
  - up to 18% at the FHWA Turner-Fairbank testbed;
  - 14% at Richmond CA with fixed signals;
  - 12–28% reported for EAD along signalized corridors.
  - Mostly single equipped vehicles, testbeds, light traffic.
  - Sources: https://www.cert.ucr.edu/media/8361/download, https://www.fhwa.dot.gov/publications/research/operations/15011/15011.pdf, https://escholarship.org/content/qt1p41x4fb/qt1p41x4fb.pdf
- **B-GLOSA for buses (Virginia Smart Road):** 22.1% fuel, evaluated **only under light traffic**; under congestion the system advised stopping. https://vtechworks.lib.vt.edu/handle/10919/108859
- **Queue-aware trajectory optimisation:** large individual savings, but no significant network-wide improvement (actuated intersections). https://rosap.ntl.bts.gov/view/dot/79024
- **Penetration:** simulation reviews report network savings of up to about 7% at 100% penetration for some algorithms, and increases in total fuel below about 30% penetration on multi-lane roads. https://arxiv.org/pdf/2001.01117 (and related)
- **Freeway traffic-wave smoothing:** the CIRCLES 100-AV field test (I-24), a different context. https://arxiv.org/abs/2404.15533

**Reading.** Measured benefits of 12–22% come from free-flow, few-queue settings, where a stop can be avoided without creeping. Our grid4 peak demand is queue-dominated. The literature agrees that queues erode the benefit at network level.

## 3. Design directions that could keep a material benefit (to test, not shown)

| ID | Direction | Rationale |
|---|---|---|
| D1 | Lower demand (off-peak) | Free-flow approaches dominate, which is where field EAD gains were measured. |
| D2 | No creeping | Reward or constraint that penalises time below 5 m/s; arrive at queue discharge from a higher speed. |
| D3 | Train on PHEMlight5 fuel | The field-closer emission model, so the policy learns its real costs. |
| D4 | Higher penetration, network fuel | Followers smooth too, as in CIRCLES and penetration studies. |
| D5 | Gentle departures only | Lower acceleration, no SPaT: the cheapest design, aimed at the largest pool (high-speed acceleration). |

**"Material"** for a registered test: agent fuel upper bound < −3% under both emission models against field-matched drivers.
