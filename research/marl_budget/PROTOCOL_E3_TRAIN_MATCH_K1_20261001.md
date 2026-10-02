# Pre-specified test: does training the relay student at constant K = 1 rescue K = 1? ("train-match rescue")

Written 01/10/2026 12:18:45 EDT (`date`), before any training or evaluation below.  Trigger: user 12:1x ("train relay
at K=1 -> test at K=1"; audit Clow first).  Clow audit (configs read 12:1x): relay6Clow_st_s0/s1/s5 were trained with
capacity 'low' (K_i,t i.i.d. uniform on {1, 2, 3}) under the CONGESTION order — neither constant K = 1 nor age-first, so
they are not a control for this question.

## Arms (seeds 0–4: the first five, fixed now)
- relayCK1_st_s<s>: scripts/MARL_e3_actor_distill_v7.py, identical to relay6Cage_st_s<s>'s config (teacher set_full_s<s>,
  student delivery prefix, relay age, order agefirst, quant 4, codebook e3_payload_codebook_20260929, set actor, 500 iters,
  8 episodes / iter, buffer 40, epochs 2, minibatch 256, lr 1e-3, beta0 1, hidden 128, eval every 20, 2 threads) except
  --capacity const1 (training AND checkpoint-selection episodes at K = 1 for every receiver and step).
- relay6Cage_st_s<s> (iid-trained, existing) and distill_none_s<s> (Z, existing).
Evaluation panel: traffic seeds 3201–3264 × 8 / 16 (checked unused 12:18), used once; relay arms with
scripts/MARL_e3_ageclip_eval.py --A -1 (the plain relay path), capacities const K = 1 and iid; Z with
scripts/MARL_e3_delivery_eval_v6.py.  Endpoint and two-level bootstrap as PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.

## Rules (unit = seed, n = 5)
- TM1 rescue: at const K = 1, relayCK1 vs Z mean gain ≥ 0 AND bootstrap lower bound > −0.5 %.
- TM2 matching helps: at const K = 1, relayCK1 vs relay6Cage effect mean > 0 with lower bound > 0.
- TM3 (reported, no rule): at iid, relayCK1 vs relay6Cage and vs Z (cost of matching to the wrong regime).
- TM4 (decision level, development panel, computed before the target read): net_Z of relayCK1 at const K = 1
  (scripts/MARL_e3_negflip_probe.py) > 0 in the mean.
Interpretation fixed now: TM1 and TM2 → the K = 1 loss is mostly a training–deployment communication mismatch; TM2 without
TM1 → matching helps but the K = 1 channel itself limits the value; neither → a deeper channel problem.  Caveat recorded:
negative flips are a same-state decision effect on the relay's own states (s ~ d^R), not a whole-trajectory effect.
Launcher `scripts/RUN_marl_e3_train_match.sh`, report `scripts/MARL_e3_train_match_report.py`.
