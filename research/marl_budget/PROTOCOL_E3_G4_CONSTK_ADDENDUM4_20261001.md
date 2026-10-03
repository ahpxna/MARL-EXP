# Addendum 4 to PROTOCOL_E3_G4_CONSTK_20261001: the NET FRESH-MINUS-STALE COUNT predicts the 4×4 const-K signs
Written 01/10/2026 23:2x EDT (`date` 23:23:49 before saving), BEFORE any 4×4 const-K target run (the 4×4 chain is still training;
no 4×4 const-K row exists).  Source: 3×3 analysis of 23:1x (ledger L-239, exploratory, post hoc on known gains): over the nine
order × capacity cells, the channel-only count net = F − (copies older than 2 steps + never-heard) orders the gains with
Spearman +0.983 (B_3 −0.778; teacher-witness N gives the same ranking, ρ(N, net) = 1.0).  The 3×3 sign boundary lies between
net/8 = −0.136 (congestion cap4, −0.15 %) and −0.029 (age-first const2, +1.01 %); frozen threshold θ = −0.08 per sender in
view.  H-C (L-237): the stale threshold is relative to the receiver's TRAINING ages.
Channel-only 4×4 values (g4 composition, 15 senders in view; F = K):
| K | net_abs (stale = age > 2) /15 | net_rel (stale = age > 9, the iid training p99) /15 |
|---|---|---|
| 1 | −0.741 | −0.411 |
| 2 | −0.482 | −0.026 |
| 3 | −0.223 | +0.034 |
| 4 | +0.036 | +0.201 |
| 5–6 | > 0 | > 0 |
- C-rel (lean, from H-C): gain > 0 iff net_rel/15 > θ ⇒ K = 1 negative; K = 2, 3, 4, 5, 6 positive.
- C-abs: gain > 0 iff net_abs/15 > θ ⇒ K = 1, 2, 3 negative; K ≥ 4 positive.
Discriminating cells: K = 2 (as in Addendum 2) and K = 3 (C-abs predicts a loss where B_3-based R-abs predicted a gain).
Scored on the const-K target gains (sign of the mean over seeds; a cell whose bootstrap interval covers 0 counts as "no
sign" and is reported, not scored).  Exploratory addendum: the G1–G8 rules of the protocol and its addenda are unchanged.
