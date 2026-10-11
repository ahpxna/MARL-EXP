# PROTOCOL — M3-H3: is there a closed-loop NET-BENEFIT opportunity for a commitment selector? (04/10/2026 23:02; registered before any H3 run)

**Purpose (user audit §7 H3, §8.2).** Before any commitment-selection learner is built, measure whether choosing WHEN and HOW to commit can beat no-SPaT (R) at all, with the closed-loop response included.
- The open-loop oracle replay of C-61 does not answer this.
- A finite best-of-candidates is NOT a global ceiling. It is a lower bound on what a perfect selector over these options could get.
- **If even the best option is rarely or never a net improvement, no critic is built** (the September lesson: a positive oracle does not mean that a learner can exploit it).

## Branching design (deterministic, same prefix)

- **Base:** RL-H:k (k 0, 1) with the frozen dev fleet (L11_s13 under k0, L11_s113 under k1) and NO SPaT (= R). TRAIN traffic 0–7 (nothing here is learned; the DEV and confirmation panels are not read).
- **Situations:** decision ticks (t\*, j) of light j with t\* in [600, 3000] s.
  - (a) RECEIVER-ELIGIBLE ticks: a fleet vehicle is eligible at j (the RPC trigger condition).
  - (b) RANDOM decision ticks, as a contrast.
  - Sampled from a scan of the base run: 24 situations per (k, seed-set), half (a), half (b), with a fixed RNG seed. 96 situations in total over 2 lights × 4 traffic seeds.
- **Interventions at (t\*, j) only** (the rest of the episode = R: no other message, RL-H unchanged):

| Option | Definition |
|---|---|
| I0 | nothing (the base) |
| Z | switch NOW, and publish the onset of the next green (zero hold) |
| H5 / H10 / H15 | hold g for h s, then switch; publish the green end while held and the onset of the next green until it starts |
| P | follow RL-H: if RL-H switches now, as Z; otherwise hold to RL-H's own predicted switch h_D (as RPC F0 M0) |
| PLACEBO | the same tick, but the message is sent to an EMPTY link set and there is no hold; it must be ≡ I0 bit-identically (KH-1). The chaos floor is estimated from the spread of option differences on situations where no vehicle reaches j within 120 s (KH-2). |

- Every branch re-simulates the full episode from t = 0 with the same seed and policies (bit-identical prefix; KH-3 checks that the prefix rows up to t\* are identical).

## Outcomes (full episode, so consequences are not truncated)

- Agent fuel, agent / human / city time loss (E4 rows), as differences vs I0 for the same situation.
- Also LOCAL outcomes: the trips of vehicles that pass light j within [t\*, t\* + 180 s] (tripinfo fuel and time loss), to reduce the noise from unrelated vehicles.

## Reported

- Per option: the mean difference vs I0 (agent fuel, TL), the share of situations improved.
- **The oracle-best option per situation:** the best agent-fuel option among those with agent and human TL change ≤ +0.5 s/veh-equivalent locally. Its mean net gain and the share of situations where it beats I0 by more than the chaos floor.
- (a) vs (b) contrast: does receiver eligibility mark situations with more opportunity?
- **Predictability** (only if the opportunity is non-trivial): a leave-one-seed-out logistic / linear model of "the best option beats I0", from deployable features at t\*. Its AUC vs 0.5.
- The registered RPC cell is P under eligibility.

## Decision rule (registered)

- **OPPORTUNITY** iff the oracle-best option beats I0 on local agent fuel by more than the chaos floor in ≥ 25 % of eligible situations, AND its mean local net gain (fuel, with TL within margin) is > 0 with a bootstrap lower bound > 0.
- **Predictable** iff the leave-one-seed-out AUC is ≥ 0.65.
- Only OPPORTUNITY + predictable opens a registered net-benefit selector (step 3 of the audit), with an abstain option and ETA / random / cost-only comparators at the same intervention budget.
- Otherwise the commitment-selection branch is closed with this evidence.

## Checks

- **KH-1:** PLACEBO ≡ I0 (bit-identical rows).
- **KH-2:** the chaos floor is reported.
- **KH-3:** prefix identity. The per-second phase trace of every branch equals the base's up to t\*.
- **KH-4:** every promised end and onset is honoured (0 violations).

* 23:05 — **Outcome definition amended BEFORE any H3 run:** "local" = the AFFECTED vehicles, i.e. those whose trip fuel or time loss differs from I0 in that branch. Under determinism every unaffected vehicle is bit-identical, so the affected set carries the whole consequence of the intervention, including chaotic propagation. The sums over it equal the full-episode sum differences. The TL constraint for the oracle-best option is the mean change over affected agents and over affected humans ≤ +0.5 s/veh. The chaos floor is not separable from consequences under this definition; uncertainty comes from the bootstrap over situations, and PLACEBO ≡ I0 is checked exactly. Scripts: `CITY_m3_h3.py`, `CITY_m3_h3_sample.py`, `CITY_m3_h3_analyze.py`.
* **Queued, not run:** user 23:0x, "máy đang nặng r, đừng chạy thêm nữa, nếu có thì bỏ vào queue đi, r chờ". The job runs in `research/queue_night_20261005` after the current chains finish, one job at a time, at most 4 parallel processes inside it.
