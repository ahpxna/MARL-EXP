# PROTOCOL E3-MIXACTOR — an actor trained on mixed profiles (step-3 audit, step 5; 28/09/2026, about 12:20)

- Written before any result.
- No ledger is edited.

**Why.** Every E3 actor so far was trained with the cached-queue prefix only, so a selector's edits
put it off its training distribution. "Changing the scheduler on an actor trained with the prefix
does not help" is not yet "other communication schemes do not help".

**Actor.** `scripts/MARL_e3_actor_train_mix.py`: MAPPO from scratch, exactly as
MARL_e3_actor_train.py (the scratch recipe), except for the training profiles.
- At each training step, with probability 0.5, the profile is drawn uniformly from the B1
  candidate family restricted to +84 B over the prefix bytes. Otherwise it is the prefix.
- Capacities are exact (|S_i| = k_i) and the cap is enforced by the env.
- Checkpoint selection: greedy select-split Σ waiting under the PREFIX scheduler (the deployed
  default).
- One actor seed (3, to mirror the best scratch actor); 2000 iterations × 8 episodes.

**Downstream.** Unchanged:
- message use (G1/G2);
- continuation labels;
- selectors v1 and the four-variant ablation (v2);
- the legal-vs-privileged diagnostic (v3);
- closed loop on the pilot panel 901–916.

**Reading.**
- Compare with scratch s3 on the same panel and the same measures:
  - realised development gain, edit and harmful-edit rates, pairwise order accuracy;
  - closed-loop sel_* − prefix.
- One seed is a pilot. A positive signal justifies more seeds; nothing here is confirmatory.
