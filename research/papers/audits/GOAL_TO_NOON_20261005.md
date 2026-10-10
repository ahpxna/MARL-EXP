# GOAL: by 12:00 on 05/10, a methods paper draft with confirmed evidence (set 01:46; user: "tập trung vào phần thực dụng nhất để hoàn thành đến đích … hoàn thành tất cả trong trưa mai")

## Destination (unchanged)

A METHODS paper on staged upgrades of two learned populations (learned lights × learned car fleets).

**Candidate method:** TSI, a two-sided interface (PROTOCOL_CITY_TSI_20261005).
- When the learned light is upgraded, neither population is retrained.
- The fleet gets a state-conditioned forecast (exact where the schedule is determined).
- The light gets a demand adapter, so that the eco fleet's slow approach is not hidden from it.

The story that the evidence supports so far:
- publishing SPaT changes the fleet's approach;
- that hides demand from the halting-based light;
- the light holds the other green;
- the forecast target shifts (C-99, C-100, C-107, C-109).

## Must-have by noon (the minimum for a defensible methods paper)

| # | Item | How | When |
|---|---|---|---|
| 1 | **TSI confirmation verdict** (5 lights × 4 fleets × 20 traffic, one attempt) + KT-1 | queue 032f, 033 | ~01:55 |
| 2 | **Component reading:** TSI − HYB (light-side value), TSI − ADP (fleet-side value) | in the confirmation report | ~01:55 |
| 3 | **Strong same-rights comparators**, registered before their runs: (a) a tuned adapter-only (best (A, B) without SPaT, chosen on SELECT); (b) the best single-sided service (HYB; N4 gates are already rejected) | SELECT grid → the confirmation panel | queue by 02:10 |
| 4 | **Retrain reference (more rights):** F1-B fleets on the same confirmation lights / traffic, so the comparison is same-panel | queue | by 02:10 |
| 5 | **One shift condition:** TSI frozen, demand +25 % (fresh routes) on lights t4–t8 × fleets s213–s513, vs R | registered, queued | by 02:30 |
| 6 | **Costs:** forecaster fit (episodes, seconds), sensors (speed bins on served lanes), inference per query, activation | from logs | writing |
| 7 | **Collision / citation pass** (04:52 research order): FoRL, HONEST-CAV, DHCP, DC-Ada, integrity gating, performative prediction / risk control, SPaT forecasting, eco-driving × adaptive signals, plus pure-math sources (performative stability / fixed points, Blackwell comparison) | web + papers | 04:52–05:51 |
| 8 | **Manuscript:** update `paper_two_population.tex` (M3 = TSI method, results, figures, limitations; abstract only from confirmed rows), compile. **User 01:50: start writing only at 05:00, AFTER the research** | writing | **05:00**–11:00 |
| 9 | **Final audit:** every number traced to a report; corrections; Vietnamese summary | — | 11:00–11:51 |

**If the TSI confirmation FAILS:**
- Report it as-is.
- The variants (037, registered) and the comparators still run.
- At most ONE second registered confirmation, on reserved traffic 720–739, of a variant chosen on SELECT.
- The paper is then written around the mechanism plus the best method, with honest scope.

**Not on the critical path (only if the queue is empty):**
- N8 CDC (queued);
- H4 / H5 fleet-side fine-tunes;
- H-PATH;
- N2 on spider;
- Lean.

## Status 01:48

- **TSI confirmation FAIL** (agent TL +0.85, upper +1.27); every other endpoint improved (C-114). KT-1 PASS.
- **TSI-2** (per-light adapter tuning, α = 0.025, traffic 720–739, with an F1-B same-panel reference) queued after N8 (C-115).
- Must-have items 3 and 4 are folded into TSI-2: HYB / ADP2 ablations, F1-B on the same panel.
- Item 5 (demand shift) is to be queued after TSI-2.

**User 01:50:** "từ 5h sau khi research hẵn viết". No manuscript writing before 05:00.
- Before 05:00: experiments, queue, checks.
- 04:52: research.
- 05:00 onward: writing.

## Status 02:36

**M3 MET by TSI-2** (C-118). Agent fuel −3.85 %, city TL −0.55, agent TL −0.22 (97.5 % upper +0.04), human TL −0.89.
- It ties F1-B on fuel and beats it on time on the same panel.
- Still running: variants (037), SHIFT (038), GEN (039).
- Writing starts at 05:00, after the research.

## Status 05:26

- Draft written: abstract, introduction, M3 = TSI, related work, limitations, references; it compiles.
- Number audit: 94 / 94 numbers in the abstract and M3 appear verbatim in the reports or the ledger. This is a presence check, not a semantic check.
- Remaining:
  - a semantic read-through (each number in its right context);
  - verify the references;
  - update the Setting section with the confirmation panels;
  - the final Vietnamese summary at 11:51.

## Status 08:47: PAPER FREEZE

- Experiments closed. Claim map locked (CLAIM_MAP_TSI_20261005.md).
- Manuscript corrected per PAPER_FREEZE_ASSESSMENT (C-125).
- Remaining (text only):
  - the layout overfulls;
  - the reference details still unverified;
  - the final Vietnamese summary at 11:51.

- 09:01: text finishing: 0 overfull; 12 references verified, numbered; Table 2 (all TSI tests, one convention); GEN teleport gap checked from the saved rows (within the limit; C-126). Remaining: the final read-through; the 11:51 summary.

- 10:07: full read-through done (C-127): 13 groups of text corrections, none changes a verdict; 179/179 numbers present; 0 overfull. The 09:51 wake was missed (the alarm was killed when the previous session ended, plus the session limit until 09:50); alarm re-armed for 10:51 at 09:59.
