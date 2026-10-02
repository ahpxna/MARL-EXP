# Pre-specified ARCHITECTURE CONTROL: is the constant-K = 1 reversal specific to the mean-pooling set actor?

Written 01/10/2026 20:10:52 EDT, before any training or evaluation below.  Trigger: user 20:0x ("lỡ như ... là do
architecture?").  Facts fixed now: the set actor (SetActorNet) mean-pools φ(sender block)·heard / (Σ heard + 1); it can represent
Z exactly (relay net with Z weights and φ ≡ 0 reproduces Z 8/8); the same architecture trained at K = 1 has positive dev net_Z
(TM4, seeds 0–1).

## Arms (seeds 0–2, fixed now)
- relayAttnCage_st_s<s>: scripts/MARL_e3_actor_distill_v8.py --arch attn (AttnActorNet: attention pooling, query from the receiver's
  own block, keys from φ(sender block incl. age) — a learned reliability weighting);
- relaySCCage_st_s<s>: --arch sharedconcat (per-slot encodings concatenated, no pooling, no dilution);
  both otherwise identical to relay6Cage_st (teacher set_full_s<s>, prefix delivery, relay age, order agefirst, quant 4,
  capacity iid, 500 iters, defaults);
- relay6Cage_st_s<s> (mean pool, existing) and distill_none_s<s> (Z).
Evaluation: panel 3601–3664 × 8/16 (checked unused 20:10), used once; scripts/MARL_e3_delivery_eval_relay_v6.py at const1,
const2 and iid (age-first, relay age, quant 4); Z with scripts/MARL_e3_delivery_eval_v6.py.
## Rules (per architecture; n = 3 seeds, per-seed outcomes reported)
- AC1 generic: mean gain vs Z < 0 at const K = 1 AND > 0 at iid, with ≥ 2/3 seeds losing at K = 1 → the reversal is not
  specific to mean pooling.
- AC2 specific: mean gain vs Z > 0 at K = 1 with ≥ 2/3 seeds winning → the reversal is a vulnerability of mean pooling.
- AC3 (reported): architecture vs mean-pool paired effect at K = 1 and iid.
Interpretation fixed now: AC1 for both alternatives → the claim "under this receiver architecture" can be widened to
"under the tested receiver architectures (mean / attention / per-slot)"; AC2 for one → the paper states an
architecture-specific vulnerability and the channel predicate tells WHERE robust aggregation is needed.
Launcher scripts/RUN_marl_e3_arch_control.sh, report scripts/MARL_e3_arch_control_report.py, both written before the runs.
