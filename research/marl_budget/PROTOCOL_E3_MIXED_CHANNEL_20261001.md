# DRAFT, NOT ACTIVE — can one receiver cover the channel's whole feasible set? (mixed-channel training)

Written 01/10/2026 21:5x EDT (`date` 21:53:18), BEFORE the train-match (TM1–TM4) and architecture-control results are
read.  Status: DRAFT.  It is activated only (i) after TM1–TM4 are reported and (ii) with the user's go-ahead (cost below).
Any change made at activation is written as an addendum with its own timestamp.

## Question (operating-envelope framing)
Train-match moves R_θ toward the K = 1 corner of F(κ).  If R_θ is a BAND (P-UP2), a K = 1-trained receiver loses on better
channels.  Can a single receiver trained on a mixture of channel regimes be compatible with the whole F(κ) of the 3×3 grid
(iid, const K = 1, 2, 3) — i.e. is the K = 1 failure a training-support problem, not a capacity limit of the receiver?

## Arm (fixed now)
relayMIX_st_s<s>, s = 0–9: scripts/MARL_e3_actor_distill_v7.py recipe (teacher set_full_s<s>, prefix delivery, relay age,
order agefirst, quant 4, 500 iterations, defaults) with the capacity of EVERY training and select episode drawn uniformly
from {iid, const1, const2, const3} by the episode seed.  Needs a new capacity mode `mix` (a v9 of the trainer, smoke-tested
against v7 at each single regime first); no other change.
Comparators: relay6Cage_st_s<s> (iid-trained), relayCK1_st_s<s> (K = 1-trained, seeds 0–4), Z = distill_none_s<s>.
Panel: a new unused traffic panel × 8/16, used once (chosen and checked at activation); conditions iid, const1, const2,
const3; endpoint and two-level bootstrap as in PROTOCOL_E3_TRAIN_MATCH_K1.

## Predictions (fixed now)
- MX1 coverage at K = 1: relayMIX vs Z mean ≥ 0 with bootstrap lower bound > −0.5 % (as TM1).
- MX2 no cost at iid: relayMIX vs relay6Cage at iid mean ≥ −0.3 %.
- MX3 dominance over the specialist: relayMIX ≥ relayCK1 at iid (where P-UP predicts the specialist pays) and within
  0.3 % of it at K = 1 (seeds 0–4).
Reading fixed now: MX1–MX2 → one receiver can be made compatible with the whole feasible set of this channel, so the K = 1
failure is training support, not receiver capacity; MX1 failing while TM1 holds → the receiver has to specialise (a
genuine band with a capacity limit).

## Novelty and cost
Training under randomised channel conditions is standard (latency sampled 0–500 ms in collaborative perception; bandwidth
variation in IMAC-type work); this arm is a test of the framing, not a method claim.  Cost: 10 trainings × ≈ 3 h under the
current load (≈ 30 core-hours) plus 40 evaluations; not to be started while the 4×4 chain, train-match and the
architecture control are still training.
