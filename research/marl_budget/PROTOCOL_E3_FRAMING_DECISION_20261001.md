# Pre-specified framing decision: which paper claim follows from which outcome (written BEFORE the outcomes)

Written 01/10/2026 21:0x EDT (`date` 20:59:37 before writing; saved 21:00).  Pending, unread: architecture control
(PROTOCOL_E3_ARCH_CONTROL_20261001, AC1 / AC2, attention and shared-concat, seeds 0–2), train-match
(PROTOCOL_E3_TRAIN_MATCH_K1_20261001, TM1 / TM2 / TM3), 4×4 const-K (PROTOCOL_E3_G4_CONSTK_20261001 + Addenda 1–3).
Purpose: fix now how each combination is worded, so the framing is not chosen after the results.  The rules of the
three protocols are unchanged; this file only maps their verdicts to claims.

## Fixed parts (do not depend on the pending outcomes)
- Channel side (Lean, `LeanMarlReceiverFloorV1/V2`): a supporting lemma, not the headline.  Novelty (21:0x, below): the
  homogeneous counting is of the Farazi–Klein–Brown type; what is ours is the prefix decoding with full-table piggyback,
  the sharp K·n (not (K+1)·n) and the heterogeneous Σ K* form, used as a pre-deployment predicate.
- Causal evidence that the channel-induced stale tail removes communication value at fixed K, bytes and fresh count:
  hold-r prospective (L-228: HD1, HD3, HD4; HD2 sign only).
- Learner-side mechanism: age-feature extrapolation shown by intervention (age-response probe, L-227, exploratory).
- Never claimed: "stale information is intrinsically harmful"; decision-level acceptability or net_Z as a surrogate for
  closed-loop return (H6).

## Mapping
| arch control | train-match | headline claim |
|---|---|---|
| AC1 for both alternatives | TM1 and TM2 | Channel-induced view shift breaks the tested receiver architectures alike, and training on the deployment channel removes it: a train/deploy COMPATIBILITY failure that the channel predicate locates before deployment. |
| AC1 for both | TM2 without TM1 | Same, but matching only reduces the loss: the K = 1 channel also limits the value of communication. |
| AC1 for both | neither | A channel-level limit across architectures; repair must come from the scheduler where the predicate allows it, and is impossible where it is forced. |
| AC2 for at least one | any | Architecture-specific: the shift exposes a vulnerability of mean pooling (and of whichever alternative also fails); the predicate says WHERE robust aggregation is needed.  Not a generic learned-communication result. |
| neither AC1 nor AC2 for an alternative (mixed seeds) | any | No claim about that architecture beyond "inconclusive at n = 3"; the paper states the mean-pool result only. |
4×4: if the const-K target fails (G1–G3 of the 4×4 protocol), every row above is restricted to the 3×3 grid.

## Follow-up fixed now (each needs its own protocol and novelty check before any run)
- TM1 holds → the deployable version is training without knowing the deployment trace: relayed-age augmentation over the
  range the floor forces at the lowest planned capacity.  Collision search first (delay / age randomisation in MARL).
- AC2 holds → compare against a reliability-weighted aggregator (ADMAC-style) before claiming a fix.
- Any branch → generality beyond CityFlow (a second domain) is the main missing piece for an empirical claim; its cost is
  estimated before it is planned.

## Addendum 1 — predictions on TM3 written BEFORE it is read (`date` 21:13:14 EDT, 01/10; train-match INCOMPLETE, 12 items
missing, no target row opened)
TM3 (train-match protocol: "reported, no rule") compares relayCK1 (trained at const K = 1) with relay6Cage (trained at iid)
and with Z at iid.  Hypothesis H-B ("capacity non-monotonicity of a fixed learned receiver"; age-response probe L-227: the
iid-trained student is worse at an unseen FRESHER age label, 0.809 vs 0.944): a receiver trained on a poor channel is
out of support on a better one (more fresh entries per step, younger relayed copies).
- P-UP1: relayCK1 vs relay6Cage at iid, mean over seeds 0–4 < 0.
- P-UP2 (the strong form, "an upgrade hurts"): relayCK1's gain vs Z at iid < relayCK1's gain vs Z at const K = 1.
Both exploratory; neither changes TM1 / TM2.  P-UP2 true → state "for a fixed learned receiver the value of communication
is not monotone in channel capacity" (with LeanMarlImitationGapV1 as the theory: the Bayes value is information-monotone,
the imitation optimum is not).  P-UP2 false and P-UP1 true → only "matching costs at iid".
