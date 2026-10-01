# MARL / E3 — directions (a) and (b) worked through (29/09/2026, started 17:48 EDT, clock-checked; updated below)

User request (16:5x): work without stopping on (b), on (a), on parallel experiments, research, and re-reading old assets.
Ledger ids L-90 … in `MARL_SELF_AUDIT_LEDGER_20260928.md`.  Evidence class: development and diagnostic.  Nothing here is
preregistered.  The panel is 901–916 × headways 8/16 (the closed-loop development panel), unless stated.

## 0. How the agents communicate (read from code, answering the user's 16:5x question)
- Messages are STATE reports (25 B: id, measurement time, phase, time in phase, and vehicles and waiting per approach).
  They carry no actions, intentions or commands.
- A public scheduler commits a global order of senders: never-heard first, then by the waiting in its OWN cached copy.
  Receiver i, with capacity K_i ~ U{1..7}, decodes the first K_i others.  The stream is one broadcast.
- Each actor, a shared MLP 2×128 tanh, maps its own sensor plus, per other agent, [fresh, heard, age, cached payload,
  static topology] to one of 9 phases.  Policies are frozen at execution.
- L-90, the implicit channel:
  - Because the prefix sends the most-congested first, the `fresh` flag is itself a congestion cue: 7.93 vs 3.05 waiting.
  - Pattern-only perturbations change 9–21 % of the scratch s3 actor's actions; content permutation changes 43 %.

## 1. Direction (a): value of the induced action change — against a zero-byte baseline (L-91)
- Zero-byte rule: each agent overrides its action by the per-agent Q̂ of Route 2, which reads only its own input.
  Restricted to the single changes a message can induce: DEV 3-step gain +2.73 (argmax), +2.04 (τ rule).
- Message steering with the candidates' TRUE induced actions (a perfect response model): +2.88 (argmax), +2.75 (τ rule).
- So even perfect response prediction adds nothing measurable over a zero-byte local override (48 states, scratch s3).
- Reading: (a) as "the value of the action a message induces" does not isolate a communication benefit.  Any such method
  must be reported against this baseline and would likely tie it.

## 2. Direction (b): send less, keep every decision
### 2.1 Lean (L-92): `work/p13_conjectures/LeanMarlDecisionCertificateV1.lean` (compiled; standard axioms; ungated)
- Identical joint actions ⇒ identical physical trajectory and cost, whatever the caches did.
- `2ε` argmax stability (Lipschitz form); the threshold is sharp.
- LIFETIME certificate: the margin condition must hold at every step before T, with the ACTUAL future caches, against
  the reference state.
- A counterexample: invariance of the current action alone does not certify a skip.
- A satisfiable instance with a stale cache (the theorem is applied to it).
### 2.2 Oracle upper bound (`MARL_e3_zero_loss_truncation.py`; self-checks)
- The reference reproduces each actor's saved closed-loop prefix row.
- Every H = end run has the reference queues at every step exactly.
- Results: see §4 (filled when all 11 actors finish).
### 2.3 Can a legal rule find the droppable packets?
- Sound certificate (L-94): interval bounds certify single-packet drops for 7.7 % of (receiver, slot) pairs at a
  ±1.5-vehicle content drift, and 1.8 % at ±3.  That is before requiring every decoding receiver, and before the future.
- Learned predictor (L-95): AUC 0.68–0.71; precision about 0.5 for scratch and mix among the top 10 % scored.
- Legal closed-loop rules (v1, 11 actors; v2, 128 episodes, fixed-cap blind curve, exact current-step oracle rule):
  see §4.
### 2.4 Literature: the novelty (b) would need
- Sender-side "send only if new":
  - TMC (Zhang, Lin, Zhang, NeurIPS 2020, arXiv 2010.14391);
  - ETCNet (Hu et al., TNNLS 2021, arXiv 2010.04978; learned gates under a bandwidth penalty);
  - Gated-ACML (Mao et al., AAAI 2020, arXiv 1912.05304; about 70 % of messages pruned for about 10 % reward loss).
- CROP (Wu et al., ICLR 2022, arXiv 2106.09292) certifies per-state actions and cumulative-reward bounds under
  observation perturbations.
- None of them guarantees an IDENTICAL trajectory.  (b)'s only defensible novelty is the decision-preserving guarantee
  including the future cache: the exact oracle bound plus the Lean statement.  A legal method reaching it is missing.

## 3. The information ceiling (running)
- `MARL_e3_actor_train_delivery.py`, identity-checked against the resume trainer.  Actors under:
  - full delivery (225 B/step);
  - no delivery;
  - a random base order (the L-90 side channel removed).
- `MARL_e3_delivery_eval.py` evaluates them on the panel under each rule.
- Purpose: bound what ANY scheduler at the prefix's bytes could gain with a co-trained actor.

## 4. Results (to be filled)

### 4.1 (b) oracle upper bound, 11 actors (L-100; 18:1x)
- Exact zero-loss (every action identical to the end; waiting identical, checked):
  - tail truncation: BC 20–26 %, mix 11 %, scratch 9–11 % of bytes;
  - greedy removal: BC 35–41 %, mix 22 %, scratch 17–22 %.
- The current-step-only exact rule saves 32–57 %, but waiting moves +0.2 … +16 % (CI > 0 for 7/11 actors).
  At 56–68 % of steps it would cut more than the lifetime check allows.
### 4.2 (b) legal closed loop (L-97 v1: 11 actors × 32 episodes; L-98 v2: 5 actors × 128 episodes)
- Blind truncation (lowest-priority packets dropped, or a fixed cap) is significantly harmful at every level.
  Cap 7 (9 % saved) already costs +0.1 … +1.6 %.
- The receiver proxy (1-byte legal report) is better than blind truncation at the same bytes for every v2 actor:
  −1.4 … −9.4 pts.  It captures most of what the exact current-step rule gets (−1.5 … −10.4).  It is not free:
  +0.8 … +4.2 % waiting at 30–58 % saved.
- With a staleness bound (also send packets whose copy at a decoder is ≥ s seconds old, from the legal mirror):
  - BC, s = 60: 19–21 % saved at −0.1 % / −0.4 % (CIs within [−1.4, +0.7]); blind at those bytes costs +1.8 / +4.4 %;
  - scratch, s = 40: 7–8 % saved at +0.1 / +0.4 % (upper bounds +1.0 / +1.3);
  - mix, proxy: 33 % saved at +0.8 % [−0.3, +1.8]; blind at those bytes costs +10.5 %.
- These are about 75–80 % of the tail-oracle saving, with no identity guarantee.
- TMC (sender-side) reaches 16 % for BC at +0.7 … +0.9 %, and ≤ 3 % for scratch and mix.
### 4.3 What this does and does not show
- Shows:
  - a legal, decision-aware truncation reaches waiting indistinguishable from the prefix at 7–33 % fewer bytes
    (actor-dependent);
  - blind truncation and TMC at the same bytes are worse or save little;
  - the gap to the exact oracle is modest.
- Does not show:
  - a certified saving: the Lean identity theorem covers only the simulated certificate; L-94 shows that sound
    legal certificates certify almost nothing for these actors;
  - a confirmatory result: all of this is development data, and the staleness bounds were adjusted once after a
    1-episode smoke;
  - a comparison with a BUDGET-MATCHED actor (training at cap 6 is running);
  - any waiting BENEFIT: the claim type is non-inferiority at fewer bytes, endpoint (b) of the E3 final draft.
    The draft protocol is `research/marl_budget/PROTOCOL_E3_TRUNCATION_DRAFT_20260929.md`; its endpoint choice is
    the authors'.

### 4.4 Information ceiling (L-101; 18:1x)
- A full-delivery actor (all 8 others decoded every step, 225 B/step, scratch recipe, seed 0) is 12.0 % better in
  waiting than the prefix system: [−14.0, −9.9] against the mean of the 5 scratch prefix actors, panel.
  - Under the prefix it is +2.1 %.  Prefix-trained actors given full delivery gain little or lose.
- So neighbour information IS valuable, about 12 %, to an actor trained for it.
- Why the E3 prefix system leaves it on the table:
  - the actor is trained to the prefix's selection;
  - the receiver capacities K_i ∈ 1..7 limit decoding.
- Full delivery breaks K_i, so 12 % is a ceiling without the capacity constraint, not an achievable same-protocol
  result.
### 4.5 Co-design inside the protocol (running, L-102)
- `nbr` actor: the same stream and the same K_i; receivers decode physical neighbours first among the streamed
  packets (+8 % bytes, patch cost).  Question: does a topology-aware decode rule plus an actor trained for it beat
  the prefix system at nearly the same bytes?
- `cap6` actor: the budget-matched comparator for (b).
- `none` actor: the no-communication reference.
- The full actor's stream truncated by (b)'s rules: a bytes-only view.

### 4.6 The declared s* rule on v3 (L-104; 18:4x)
- 11 actors × 128 episodes.  s* is the largest pooled saving whose upper 95 % bound on waiting is below +1.0 %.
- BC: s* = 60 → 19.4 % fewer bytes at +0.23 % [−0.50, +0.96].
- Scratch: no s qualifies (s = 40: +0.46 % [−0.11, +1.03]).
- Mix: no s qualifies.
- Applied as declared.
### 4.7 THE NO-COMMUNICATION ACTOR (L-105; 18:4x) — changes the reading of everything above
- A scratch-recipe actor trained with NO messages (0 B) is 8.0 % better than the prefix system:
  - [−8.6, −7.4] over 128 episodes;
  - it beats every one of the 5 prefix actors.
- The full-delivery actor is only 2.5 % [−3.7, −1.4] better than the none actor, and it needs 225 B/step and
  unconstrained receivers.
- Readings:
  - On E3, a trained actor gets about 2.5 % from neighbour messages at most.
  - Under the protocol's random receiver capacities and the prefix, the messages make learned actors worse than
    ignoring them.
  - Every selector (L-65 …) and truncation (L-97 … L-104) result was measured on actors that a zero-byte actor beats.
  - (b) remains meaningful only for a FIXED deployed actor.  As a system claim it is dominated by the none actor
    (0 B, −8 %).
- A communication-METHOD claim on E3 must beat the none actor inside the protocol.  Running:
  - `nbr` (neighbour-first decoding);
  - `nbrmask` (neighbour-first decoding and non-neighbour slots masked in the actor input);
  - `cap6`;
  - second seeds of none and full.

### 4.8 Co-design inside the protocol, and replication (L-106 … L-109; 19:0x)
- Budget-matched cap6 actor (149 B/step):
  - −4.7 % against the prefix system, which beats every truncation of prefix-trained actors;
  - +3.8 % against the none actor.
- nbr actor (neighbour-first decoding, 204 B/step):
  - −2.1 % against the prefix system;
  - it does the same under the prefix (−2.2 %), so it does not use the neighbour-first information;
  - +6.5 % against the none actor.
- The none actor replicates: seed 1 −7.9 % against the prefix system; seed 1 vs seed 0 +0.2 %.
- The consistency rule so far: none (0 B) < full (225 B, capacity broken) is the only ordering where messages help.
  Every capacity-respecting delivery tried (prefix, cap6, nbr) is worse than none.
- Open, running:
  - nbrmask: non-neighbour slots masked in the actor input;
  - full seed 1;
  - 4000-iteration continuations of the prefix and none actors (does communication only learn slower?).

### 4.9 Equal training, the masked co-design, seeds (L-110 … L-113; 19:3x)
- The full actor is seed-dependent against none: −2.5 % (s0) and −8.6 % (s1).
- nbrmask (neighbour-first decoding and non-neighbour slots masked) ties none: −0.2 % [−1.1, +0.7].  It does use the
  neighbour information (+2.4 % better than under the prefix).
- At 4000 iterations the prefix actor is still +6.3 % worse than the none actor at 4000, and worse than the none actor
  at 2000.
- Running: set-structured actor (prefix, nbr); nbrmask seed 1.

## 5. Where this leaves the rescue question (19:3x)
1. Scheduler-side methods on a frozen prefix-trained actor ((a), the selectors, (b)): at best tie their own
   baseline.  They are all dominated by a no-communication learned actor.  (a) ties a zero-byte override.
   (b) is non-inferior only for BC actors.
2. The value of communication exists only for an actor trained with FULL consistent delivery: 2.5–8.6 % over none.
   It breaks the receiver capacities.
3. Inside the capacities, co-design so far reaches a TIE with none (nbrmask).  The set-structured actor is the last
   actor-side attempt running.
4. If nothing inside the protocol beats none, the honest paper is an analysis paper:
   - the oracle headroom is action perturbation;
   - the fresh-flag side channel;
   - the zero-loss/lifetime bound with its Lean certificate;
   - consistency beats quantity;
   - a 0-byte actor beats every prefix-communicating actor on this protocol.
   That is a publishable negative with mechanisms.
