# PROTOCOL E3-SCRATCH — an actor NOT warm-started from MP2 (28/09/2026, 00:45)

- This is a companion to `PROTOCOL_E3_PILOT_20260928.md`. That file is left unchanged, because the
  running chain checks its hash.
- Written before any scratch-actor label, selector or closed-loop result exists.
- The only scratch result seen is the pilot training curve `e3_actor_s0_20260928_002644`
  (600 MAPPO iterations): best select 1811 against MP2 1730.
- No ledger is edited.

**Why.** The pilot protocol declares that the BC + MAPPO actor is not independent of MP2. This
variant removes the MP2 warm start.

**Actor.** `scripts/MARL_e3_actor_train.py`, unchanged.
- MAPPO from random initialisation, 2000 iterations × 8 episodes.
- Checkpoint selection on select every 20 iterations.
- Actor seeds 0, 1, 2.
- Same adapter, reward, splits and critic as the pilot.

**Everything downstream is identical to PROTOCOL_E3_PILOT §2–§4:**
- message use on development;
- continuation labels with the scratch actor as π and as the continuation;
- selectors with and without the bid;
- the closed-loop pilot panel 901–916 with direct and R1;
- the report and fig3.

Runner: `scripts/RUN_marl_e3_long_scratch.sh` (a copy of the pilot runner with only the actor
stage changed; 3 label shards).

**Gates and reading.**
- G1 and G2 as in PROTOCOL_E3_PILOT §5, applied to the scratch actor of each seed.
- Seeds 1301–1316 stay reserved.
- Nothing here is confirmatory.
