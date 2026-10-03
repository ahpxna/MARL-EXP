# Pre-specified tests of the NET FRESH-MINUS-STALE COUNT (findings 1–3), the provisioning rule (A) and a count-deadline
# order (B) — written before any run below

Written 01/10/2026 23:4x EDT (`date` 23:41:11 before writing).  User 23:3x: "làm 1 2 3 và A với B đi".  Source: L-239
(exploratory, post hoc on the nine order × capacity cells): net = F − (copies older than 2 steps + never-heard) per
receiver-step, Spearman +0.983 with the gain vs Z; the stale COUNT beats the stale BURDEN B_3; the timed floor bounds net.

## Frozen now (not to be re-fitted)
- Functional: net = F − S_τ − N, F = entries delivered directly this step, S_τ = merged-view entries older than τ = 2
  decision steps, N = never-heard; per receiver-step mean over the cell; normalised net / (m − 1).
- Sign rule: gain vs Z > 0 iff net/(m − 1) > θ = −0.08 (the 3×3 midpoint of L-239).
- Training-relative version for a receiver trained on a channel whose relayed ages reach τ_train: S_{τ_train} instead of S_2
  (3×3 iid-trained τ_train = 2; K = 1-trained τ_train = 8; 4×4 iid-trained τ_train = 9).

## Part 1 — findings 1 and 2 OUT OF SAMPLE on the hold-r cells (no new policy run)
Channel-only composition of the hold-r schedules (scripts/MARL_e3_channel_composition_probe_v2.py, fixed actions; at
constant K the composition does not depend on the policy), development episodes 901–904 × 8/16.  SELF-CHECK: with
--order agefirst --hold 1 it must reproduce MARL_e3_channel_composition_probe.py's g3_nopolicy numbers (entries, never, B3,
age histogram) exactly.  Cells: the nine hold-dose development cells (K, r) = (1, 1), (2, 1/2/3/4/6), (3, 1/4/6) with their
known development gains (e3_hold_dose_report), and the six prospective cells (2, 1/3/4/6), (3, 1/6) with their known
prospective gains (e3_hold_prospective_report, panel 3501–3564).  The functional and θ were fixed on other cells, so these
cells test them out of sample (the gains are known; the coordinate values are not yet computed).
- N1: Spearman(net, gain) over the nine development cells ≥ +0.80 and ≥ |Spearman(B_3, gain)| (−0.833 in that report).
- N2: the frozen sign rule classifies ≥ 5 of the 6 prospective cells (sign of the mean gain).
- N3 (count vs burden): |Spearman(S_2 + N, gain)| ≥ |Spearman(B_3, gain)| over the nine development cells.

## Part 2 — the theorem bound on the coordinate (Lean, no run)
work/p13_conjectures/LeanMarlNetFloorV1.lean, corollary of LeanMarlReceiverFloorV1.timed_floor (n = 1) and
timed_forced_stale (n = τ + 1): for every scheduler, relay content and memory, at constant capacity K,
  fresh + (m − 1) ≤ K (τ + 2) + stale_τ,   i.e.   net ≤ K (τ + 2) − (m − 1)
(never-heard senders are in stale_τ since their last-measured time is 0).  Compiled with standard axioms before use.

## Part 3 — A: the provisioning rule (derived, then scored on existing and pending cells)
From Part 2 and the sign rule: under constant capacity K a receiver with training range τ_train can be kept on the positive
side by SOME scheduler only if K (τ_train + 2) − (m − 1) > θ (m − 1), i.e.  K > K_min := (1 + θ)(m − 1) / (τ_train + 2).
(For time-varying budgets K is replaced by the richest-receiver budget averaged over the window, via LeanMarlReceiverFloorV2
and LeanMarlPrefixInstanceV1.)  Necessary, not sufficient: the scheduler must also attain the bound (age-first does within
0.1–0.8 copies, L-239) and the receiver's lower band edge (too fresh) is not covered.
- A1 (existing, scored now): 3×3 iid-trained (τ_train 2): K_min = 1.84 ⇒ K = 1 forced negative, K = 2, 3 allowed —
  matches the signs of the const-K gains (−1.65 / +1.01 / +1.72 %).  K = 1-trained (τ_train 8): K_min = 0.74 ⇒ K = 1 allowed —
  matches the interim relayCK1 gain (+2.61 %, L-238; scored finally on TM1).
- A2 (pending, 4×4, as Addendum 4): iid-trained τ_train 9: K_min = 1.25 ⇒ K = 1 forced, K ≥ 2 allowed (C-rel); with the
  absolute τ = 2: K_min = 3.45 ⇒ K ≤ 3 forced (C-abs).

## Part 4 — B: the count-deadline order (channel-only first)
models/marl_delivery_countdeadline.py: CountDeadlineDelivery(τ): senders ordered by u_j = number of receivers whose copy of
j (scheduler mirror, the AgeMirror of every E3 order) is at least τ steps old or absent, most first, ties by the age-first
key — an order that targets the COUNT of out-of-support copies.  Scheduler information only.
Channel-only composition under --order countdeadline<τ>, τ ∈ {2, 3}, vs age-first, capacities iid, cap4, low, const1–3.
- B1 (theory, a check that can fail): at constant K the reduction of S_2 + N is at most the room above the floor measured for
  age-first (≤ 0.12 at K = 1, ≤ 0.23 at K = 2, ≤ 0.78 at K = 3).
- B2: a closed-loop test is written (separately, before any run) only for capacity cells where countdeadline lowers S_2 + N
  by ≥ 0.2 copies per receiver-step relative to age-first; otherwise B is reported as "no room" (the theorem's prediction at
  constant K).

## Addendum 1 — E3: heterogeneous budgets (written 02/10/2026 01:1x EDT, `date` 01:12:33, before the run)
Channel-only composition v2 (now with rich<k> / bursty / high / fixed built exactly as the evaluators do, and the hub order
of models/marl_delivery_music_v4.py), development episodes 901–904 × 8/16, cells: {agefirst, countdeadline3} × {rich7,
bursty, high, fixed, low, iid} and hub × {rich7, low}.  Heterogeneous floor at each step t (LeanMarlReceiverFloorV2 /
PrefixInstanceV1): senders with age ≤ 2 at a receiver ≤ Σ_{s = t−2..t} K*(s), so stale(>2) + never ≥ (m − 1 − ΣK*)_+;
slack = measured (stale + never) − mean bound.
- E3a (out of sample, one cell): the frozen sign rule net/8 > −0.08 on rich7 age-first predicts the sign of its known
  development gain (+0.65 %, 7/10 seeds; PROTOCOL_E3_RICH7_CONTROL, exploratory).
- E3b: where the heterogeneous floor is loose (rich7, high, bursty) the count-deadline order lowers stale + never by ≥ 0.2
  copies in at least one cell (scheduler slack exists only where the bound does not bind), and the hub order lowers it in
  rich7 relative to age-first.
Exploratory; no closed loop follows without its own protocol.
