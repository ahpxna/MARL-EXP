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

Note 22:1x (still DRAFT): the trainer for this arm is to be v10 = scripts/MARL_e3_actor_distill_v9.py (exact resume, L-234)
plus the `mix` capacity mode, launched through run_with_watchdog WITHOUT --out so a hang resumes in place.

## Addendum 1 — ACTIVATION (written 02/10/2026 01:4x EDT, `date` 01:48:49 before writing; BEFORE any relayMIX training or any evaluation on the panel below)
Conditions met: TM1–TM4 reported (L-250, final 5 seeds); E1 / E3 / E5 done (L-249, L-246); user go-ahead 02/10 01:0x ("kêu m làm
E4 khi nào mấy cái E trên đã chạy xong và cpu trống").  Changes and choices fixed now:
- Trainer: scripts/MARL_e3_actor_distill_v10.py = v9 + --capacity mix (the draft named v7; v10 is v7's recipe with v8's arch
  default `set` and v9's exact resume; at any single regime v10 = v9 = v8 = v7, self-checks TEST_marl_distill_v9_resume (PASS
  twice, L-234) and TEST_marl_distill_v10_mix (PASS 01:48, research/marl_budget/distill_v10_mix_selfcheck_20261002/RESULT.json:
  v10 = v9 at iid and const1, mix resume exact, mix changes training, balanced regimes, traces)).  "Drawn uniformly by the
  episode seed" is implemented as a BALANCED fixed assignment: each of iid / const1 / const2 / const3 gets exactly 32 of the
  128 TRAIN and 4 of the 16 SELECT episodes (a permutation from its own generator, seed 20261002, the same for every student
  seed); checkpoint selection = mean select queue sum over that mixed SELECT set.
- Launch: run_with_watchdog WITHOUT --out (stall 1200 s, 20 retries) and --park-if-no-state; seeds 0–9 in 4 lanes
  ({0,4,8}, {1,5,9}, {2,6}, {3,7}), --threads 2; started only when the architecture-control lanes have finished.
- Panel: traffic seeds 3801–3864 × headways 8 / 16 (checked unused 01:46 by parsing all 177 435 manifest / config files under
  research/marl_budget), used once.  Conditions K = 1, 2, 3 and iid (scripts/MARL_e3_ageclip_eval.py --K k --A -1; K = 0 =
  iid) for relayMIX_st_s0–9, relay6Cage_st_s0–9, relayCK1_st_s0–4; Z = distill_none_s0–9 (scripts/MARL_e3_delivery_eval_v6.py
  --deliveries none --capacity iid).  Endpoint, pairing and two-level bootstrap as PROTOCOL_E3_TRAIN_MATCH_K1.
- MX1–MX3 unchanged (MX1, MX2 over seeds 0–9; MX3 over seeds 0–4).  Added now, exploratory (no rule): MX4 the spread
  max_K − min_K of the mean gain vs Z over the four capacities is smaller for relayMIX than for relay6Cage and for relayCK1
  (one receiver covering the feasible set flattens the E1 mismatch curve); K = 2, 3 cells reported for every arm.
- Report scripts/MARL_e3_mixed_channel_report.py and launcher scripts/RUN_marl_e3_mixed_channel.sh written before the run.

Deviation 1 (execution only; written 02/10/2026 02:3x, `date` 02:39:42): at 02:32 every training lane stopped at its disk guard
(14 GB free < 15) after training relayMIX_st_s0–s3 (all COMPLETE); the comparator lane had finished (70 evaluations).  No
result was read.  Disk was reclaimed without deleting anything (scripts/UTIL_dedupe_hardlink.py: byte-identical scenario
dumps in finished runs replaced by hard links, every replacement logged); the same launcher is then rerun per lane
(idempotent: skips complete items), so relayMIX_st_s4–s9 and the 40 relayMIX evaluations follow unchanged.
