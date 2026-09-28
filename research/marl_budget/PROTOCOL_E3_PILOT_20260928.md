# PROTOCOL E3 — communication-aware learned actor: pilot and first multi-seed round (28/09/2026)

- Written before any E3 label, selector or closed-loop result exists.
- The only E3 output seen so far is the actor-training curves:
  - `e3_actor_s0_*`: from-scratch MAPPO, slow;
  - `e3_actor_v2_smoke_*`: BC + MAPPO smoke.
- No ledger is edited.
- Scope: PROTOCOL_HETERO_v0 with Amendment 1. That means one broadcast, heterogeneous decoding
  budgets, i.i.d. capacities, 3×3 CityFlow, zero delivery delay, cap +84 B over the prefix bytes,
  and bids charged inside the cap.

## 1. Actor (`scripts/MARL_e3_actor_train_v2.py`, `models/marl_comm_actor.py`)

- **Input.** `CommAdapter` builds receiver i's input from its own view: own sensor, own phase, the
  agent one-hot, and one block per other agent j:
  - fresh, heard, age;
  - payload: phase, elapsed, vehicles, waiting;
  - static public topology.

  A missing message is encoded as heard = 0, which is distinct from a heard zero.
- **Training.**
  - Behaviour cloning from frozen MP2 on the SAME restricted views (train split).
  - Then critic warm-up.
  - Then MAPPO (PPO clip 0.2, GAE 0.99/0.95) on the team reward −(total waiting)/100.
  - The centralised critic uses a privileged global state, in training only.
- **Checkpoint selection.** Greedy sum of waiting on the select split.
- **Splits.** Train 301–364, select 401–408, development 501–508 (headways 8, 16).
- **Actor seeds.** 0, 1, 2. Seed 0 is the pilot.

## 2. Evaluator target and labels (`scripts/MARL_e3_continuation_labels.py`)

- **Target.** cont_3(S) − cont_3(P). Profile S is transmitted at step t; steps t+1 and t+2 run the
  declared continuation (prefix scheduler + the same frozen actor, greedy). The base trajectory is
  prefix + actor.
- **States.** Train split at t ∈ {7, 10, 13, 16, 19, 22}; select and development at
  t ∈ {10, 16, 22}.
- **Candidates.** The B1 family on live K.
- **Self-checks.** Replay reproduces order and K; cont(P) equals the base run; access invariants
  hold on every step.

## 3. Selectors (`scripts/MARL_e3_selector_train.py`)

- **Variants.**
  - `sel_nobid`: z, K, mirror, candidate.
  - `sel_bid`: the same plus the NEW actor's 1-byte bid (top-2 phases, logit-gap bin; bin
    thresholds from train quartiles), charged 10 B.
- **Selection.** The epoch and τ are chosen on select; development is reported.
- **Init seeds.** 0, 1, 2 per variant.
- **Policies.** direct and R1.

## 4. Closed-loop panel (`scripts/MARL_e3_closed_loop.py`)

- **Panel.** Seeds 901–916 × headways 8, 16: 32 episodes. These seeds were never used before.
  This is the E3 PILOT panel; it is not a final test.
- **Methods.**
  - prefix (actor);
  - MP2 reference;
  - sel_nobid/s0–2;
  - sel_bid/s0–2.
- **Policies.** direct, and R1 in a second run.
- **Report.** `MARL_hetero_closed_loop_report.py --control sel_nobid` (full endpoints plus the
  oracle-access self-check), and fig3 v4.
- **Reserved.** Seeds 1301–1316 are kept for a later preregistered E3 test, after the design is
  frozen.

## 5. Decision rules, fixed now

**Gate G1 — the actor uses messages (seed 0, development 501–508,
`scripts/MARL_e3_message_use.py`).** Both conditions must hold:
1. The input-level action-change rate under `none` is ≥ 0.10.
2. The closed-loop sum of waiting under `none` is worse than under `actual`: mean > 0 with the
   lower 95% bound > 0.

**Gate G2 — the actor is competent (seed 0).** Its best select-split sum of waiting is within
+10% of MP2's on the same episodes.

**Reading of the selector and closed-loop results.**
- Only if G1 and G2 pass for seed 0. Otherwise they are recorded but not interpreted as a method
  result.
- Seeds 1–2 are run in the same chain to save wall time. They are interpreted only under the same
  gates.
- Descriptive panel endpoints:
  - sel_bid − sel_nobid (the bid effect);
  - sel − prefix (the selection effect);
  - R1 − direct;
  - each with a bootstrap over episodes and every init seed shown.
- No claim from this panel is confirmatory. A confirmatory claim needs a freeze plus seeds
  1301–1316.

## 6. Limits declared in advance

- The actor is warm-started from MP2, so it is NOT independent of the MP2 design.
- H = 3 continuation, not the full-episode return.
- A candidate family, not exact enumeration.
- One topology; fixed input width.
- No network delay.
