# Why do messages hurt the flat E3 actor?  Root-cause hypotheses, discriminating experiments, and improvement directions
(29/09/2026, written 22:0x EDT, before the discriminating results; ledger L-121)

## The fact to explain (L-105 … L-120; 128 episodes, development)
- A flat MLP actor (276 inputs: own 35, agent one-hot 9, 8 sender blocks of 29) trained with capacity-limited messages
  is 4–9 % WORSE than the same recipe trained with no messages.
- Fixes on the delivery side did not rescue it:
  - fixed capacities: +8.9 %;
  - random order: +9.0 %;
  - neighbour masking: seed 0 ties, seed 1 +5.0 %.
- A set-structured actor fixes most of it, even with no messages:
  - set_none is −2.7 % vs flat none;
  - set actors trained with messages are −2.3 … −3.2 % vs set_none even at 0 B (one seed; replicates running).

## D1, done (input attribution, `scripts/MARL_e3_input_attribution.py`, 7,776 real inputs)
- The flat prefix actors put 59–62 % of their decision sensitivity (|grad × input| of the top-2 margin) on message
  dims: fresh 34 %, STALE (cached) 25–28 %.  Own state gets only 29–32 %.
- Set actors: own 45–53 %, messages 35–40 %.
- So the flat actor leans on stale content about as much as on fresh content.

## Root-cause hypotheses and the experiment that discriminates each (flat unless noted; seed 0; 2000 iterations; 128-episode endpoint)
| # | hypothesis | prediction if TRUE | experiment | status |
|---|---|---|---|---|
| H1 | varying irrelevant input dimensions degrade PPO's data efficiency (cf. "data efficiency is degraded by unnecessary input dimensions") | an actor with UNINFORMATIVE random values in the message slots is as bad as the prefix actor | `rc_noise_s0`: none delivery, NoiseCommAdapter | running |
| H5 | STALE cached content misleads the decision | (i) hiding stale blocks at evaluation improves the prefix actors; (ii) a fresh-only-trained actor beats none | D2 `diag_flat_freshonly` (eval-time); `rc_fresh_s0` | (i) REFUTED 22:1x: scratch s3 +4.4 %, rs s0 +0.0 %; (ii) running |
| H3 | no WEIGHT SHARING across the 8 slots: each slot must be learned separately | a shared per-slot encoder with CONCATENATION (no pooling) recovers the set actor's gain | `rc_sconcat_s0`: SharedConcatActorNet | running |
| H4 | no AGGREGATION: a variable number of messages lands in fixed slots | shared-concat stays bad while set (mean-pool) is good | the same, against set_prefix | running |
| H7 | network capacity (2×128 for 276 inputs) | hidden 256 closes the gap | `rc_h256_s0` | queued (CPU) |
| H9 | the priority side channel | random-order training fixes it | `rand_s0` | done: NO (+9.0 %) |
| H10 | per-step capacity volatility | fixed capacities fix it | `fixcap_s0` | done: NO (+8.9 %) |

Reading rules, written now:
- H1 is supported if rc_noise is ≥ +4 % vs none_s0.
- H5 is supported if D2 improves the prefix actors by ≥ 2 %, or rc_fresh beats none_s0 (upper bound < 0).
- H3 is supported if rc_sconcat is within 1 % of set_prefix.  H4 is supported if rc_sconcat stays ≥ +4 % vs none_s0 while
  set_prefix is better.
- More than one hypothesis can hold.

## Improvement directions (from the research), each with its first experiment
1. **Aggregation architectures.**
   - Mean-pooled DeepSets is running (set actors).
   - TarMAC-style signature attention (Das et al., ICML 2019): the receiver's query weights senders.
   - First experiment: `rc_attn_s0` (running).
   - Later: GAT over the road graph, as CoLight.
2. **Communicate to learn, act with fewer bytes.**
   - Asymmetric actor-critic / privileged teacher–student (Pinto et al. 2018; the informed asymmetric actor-critic,
     arXiv 2509.26000).
   - First experiment: distil the best teacher (set_full: −7.5 % with full messages) into a capacity-limited or
     zero-byte set student by DAgger on the student's own states.
   - Needs a distillation trainer; not yet written.
   - Also the seed-1 replicates of "trained with messages, deployed at 0 B" (running).
3. **Staleness-aware inputs** (if H5 holds): age-weighted or fresh-only receiver inputs, and an explicit age embedding.
4. **Input-dimension hygiene** (if H1 holds):
   - dimension masking / redundancy reduction at the receiver (DRMAC, arXiv 2501.02888);
   - message-dropout training (Kim et al., AAAI 2019).

## What would change the MARL paper
- If a capacity-respecting design beats the same-architecture none actor at deployment, with seed-1 replication, the
  method paper is back, with an honest baseline set: none, maxq, prefix.
- If only "trained with messages, deployed at 0 B" replicates, the paper becomes a communication-as-training-signal
  result.  It needs the distillation test.
- If nothing replicates, the analysis paper stands, with the root causes above as its mechanism section.
