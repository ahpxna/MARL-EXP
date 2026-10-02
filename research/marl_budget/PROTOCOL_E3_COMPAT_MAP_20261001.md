# Pre-specified EXPLORATORY probes for the channel–receiver compatibility framing (written before any run below)

Written 01/10/2026 21:3x EDT (`date` 21:34:54 before writing).  User 21:2x: "làm những thứ phải làm cho hướng tiếp theo,
ưu tiên việc ít dùng CPU".  Framing: MARL_DIRECTION_BRAINSTORM_20261001.md and the user-pasted "operating envelope" note
(F(κ) = channel-achievable exposure set, R_θ = receiver compatibility region, repair locus = whether they intersect), with
the corrections of 21:2x: (i) the envelope is valid as a function of exposure only for STATE-INDEPENDENT stream orders
(H-A); (ii) R_θ may be a band, not a half-space (H-B, PROTOCOL_E3_FRAMING_DECISION Addendum 1).

## Part A — does staleness carry information about the sender's state? (H-A; scripts/MARL_e3_staleness_meaning_probe.py)
Design.  The driving policy is the zero-byte student Z (distill_none_s0) acting on its LOCAL view only, so the traffic is
identical in every cell of the same episode and only the channel differs.  Cells: order ∈ {agefirst, prefix (the
cached-queue congestion ranking of models/marl_delivery_music.py)} × capacity ∈ {iid, cap4, low, const1, const2}; relay v2
merge ('age'); development episodes 901–916 × 8/16 (32 episodes per cell).  Per receiver-step and per entry of the merged
view: sender j, age a (decision steps), the copy's waiting and vehicle sums, and the sender's TRUE current waiting and
vehicle sums (`env._summary(j)` read outside the no-oracle guard — DIAGNOSTIC ORACLE, recorded only).
Self-checks that can fail: (1) the per-episode queue sum is identical in all ten cells (the channel cannot reach the world);
(2) the access-invariant and mirror checks of the evaluators.
Statistic.  r_now = w_now(j, t, ep) − μ(j, t, load), with μ the mean over the 16 traffic seeds of the same (j, t, load)
(common to all cells because the world is common).  S(a, cell) = mean r_now over entries of age-bin a, bins {0}, {1, 2},
{3, 4}, {5–8}, {≥ 9}; standard errors by episode bootstrap.
Theory (fixed now).  With a world that does not depend on the channel and an order that depends only on the capacity trace
and past schedule (age-first), the age of j's copy is independent of j's state given (j, t), so S(a, cell) = 0 in
expectation for every a and capacity.  The congestion order ranks by the cached queues, so a long-untransmitted copy is
selected for a low reported queue.
- SM1 (null implied by the theory; a failure means state leaks into the age-first order): every age-first S(a, cap) has a
  95 % bootstrap CI covering 0, or |S| < 0.05 σ_w (σ_w = pooled SD of r_now).
- SM2: congestion order, S(a ≥ 3) < 0 at iid, cap4 and low (stale ⇒ currently less congested).
- SM3 (meaning shift with capacity): RMS over a ≥ 3 bins of S_prefix(a, cap) − S_prefix(a, iid), cap ∈ {cap4, low, const1},
  at least twice the same RMS for age-first, and ≥ 0.05 σ_w.
- Secondary (reported): E[r_now − r_copy | a] by cell (drift beyond the copy's content), with r_copy residualised at t − a.
Reading fixed now: SM1–SM3 hold → the "semantic" incompatibility class is real in this channel (a capacity change under a
state-dependent order changes what a stale copy means), and the exposure-only envelope must be indexed by the order.  SM2
without SM3 → staleness is informative but capacity-invariant; the congestion anomaly (B_3 over-predicts harm) is then a
relevance effect (Part C), not a meaning shift.

## Part B — the compatibility map on existing 3×3 cells (no new run; POST HOC, labelled so)
Coordinates per cell (policy-driven view statistics already recorded: e3_viewstats_v2, e3_order_dose, hold-r channel-only
B_3): fresh entries per receiver-step F, relayed entries, never-heard N, B_3, and R = B_3 / F (burden per fresh packet).
Already seen: on the hold-r prospective cells R orders the mean gains monotonically (Spearman −1.0, B_3 alone −0.943); this
is post hoc and is NOT evidence.  Frozen now for prospective use: the sign rule "gain > 0 iff R < R* = 2.3" (midpoint of
the largest positive-cell R 1.98 and the smallest negative-cell R 2.66 among the 3×3 const-K / hold cells).
- CM1 (prospective, 4×4 const K, PROTOCOL_E3_G4_CONSTK; channel-only g4 composition, F = K): R = 17.4 / 8.2 / 0.63 / 0.66 /
  0 / 0 at K = 1 / 2 / 3 / 4 / 5 / 6 ⇒ predicted sign − / − / + / + / + / +.  This coincides with the R-abs reading of
  Addendum 2 (it does not discriminate from it); it is registered so that the map is tested, not only described.
- CM2 (state-dependent order): congestion-order cells are NOT predicted by the age-first rule (expected to be milder than
  their R); if they fall on the age-first boundary, the order index is unnecessary.  Partly seen post hoc (B_3 29.7 →
  −0.15 %), so CM2 is tested only on new congestion cells.

## Part C — decision-relevant (witness) burden (defined now; run after Part A)
For receiver i at a step, sender j is a WITNESS if replacing j's copy alone by its fresh payload (counterfactual view)
changes the teacher's argmax (DIAGNOSTIC ORACLE).  D = Σ_j 1[j witness] (a_j − 3)+.  Prediction W1: over the nine
order × capacity cells of PROTOCOL_E3_ORDER_DOSE, |Spearman(D, gain)| ≥ |Spearman(B_3, gain)|, and the congestion cells
have a smaller D / B_3 than the age-first cells.  Its own probe script and smoke run come first; the cell gains are already
known, so W1 is exploratory and only a prospective cell can confirm it.
