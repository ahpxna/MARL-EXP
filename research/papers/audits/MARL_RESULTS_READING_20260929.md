# MARL / E3 — how to read every result, new and old (29/09/2026, written 11:11 EDT, clock-checked)

Style asked for by the user (10:4x): for each result, what it SHOWS, what it does NOT show, what is NOT YET SEPARATED,
and what it means for the two directions still worth weighing:
- (a) value learning with receiver–sender structure;
- (b) certificates that cut transmission while keeping the actor's decisions, including the FUTURE cache.

Ledger ids in brackets.  Evidence class: development and diagnostic unless marked preregistered.

## 0. Reading rules applied here
- An oracle's headroom is not a learner's.  A 3-step label is not the closed-loop objective.
- An offline gain is not a closed-loop gain.
- A theorem about its own model class is not a theorem about CityFlow.  Shape agreement is not proof [L-86].
- "At chance" means the tested learners failed.  It does not mean legal information is insufficient.
- Each result is tied to the actor (BC, scratch, mix), because the sign of an edit's effect depends on the actor.

## 1. New results (28–29/09)

**Normalisation defect vs closed loop** [L-65, L-69, L-70, L-78, L-85]
- Shows:
  - The E3 normaliser was broken; offline DEV was untouched.
  - With the guard, selectors remain worse than the prefix in 24/24 actor × variant cells.
  - With a floored normaliser (v8, test 1), the selectors are still worse than the prefix: scratch s3 +0.66%, BC s3 +2.25%, mix +0.63%.
- Does not show: what a well-ranked selector would do.  The guard also stops editing after the first out-of-support state.
- Not separated: none needed.  The defect is ruled out as the cause of the negative closed loop.

**Hindsight (resampled future arrivals)** [L-71]
- Shows: the stored best candidate keeps 81–89% of its 3-step gain across resampled futures, and an ex-ante choice
  reaches 93–96% of the hindsight maximum.  The oracle headroom survives changes of the random future.
- Does not show:
  - robustness to the capacity trace, which was held fixed;
  - anything beyond 3 steps.
  - A 30 s window leaves little room for arrival noise, so the result was partly predictable [L-77].

**3-step label vs full-episode return** [L-73]
- Shows:
  - Optimising the 3-step label is NOT the same as improving the episode.  Within-state Spearman(g3, g_full) is 0.39–0.61.
  - The g3 argmax captures from below 0 up to 68% of the full-episode best.
  - The best-by-g3 single edit helps the full episode for scratch (+0.6 … +2.4%) and mix (+3.1%), and is ≈ 0 for BC.
  - Random single edits: g3 ≈ −0.1 … −3.4, but the full episode is −0.03 … −2.7%.  The per-step |Δq| grows after any edit.
- Does not show: which part of the full-episode effect is the action at t, the later actions, or the cache
  (partly addressed by the revert probe below).

**Revert-after-L (cache persistence)** [L-74]
- Shows:
  - Reverting the edit's off-schedule entries after 1 step changes the random-edit harm by only 0.0 … +0.2 pp.
  - For oracle edits, the revert removes up to 0.5 pp of gain (BC s2), so some value does travel through the cache.
- Does not show: the effect of MISSING deliveries on the future cache.  This is the case that matters for direction (b).

**Forced single-agent action changes vs message candidates** [L-81]
- Shows (scratch s3, 3-step):
  - Blind forcing reaches the same oracle as message candidates that change one agent's action: +11.3 matched best-of-N vs +11.0.
  - Reaching the same (agent, action) through a message is not better: −0.54.
  - Messages that change no action at t still carry +5.4 at best, through later steps.
- Does not show: multi-agent changes, other actors, or the full episode.  It does NOT show that messages carry no information value.

**S3, the L-60 reconstruction** [L-83]
- Shows: with the true own block, the reconstruction reproduces the actor's top-1 for 324/324 receivers.  The scheduler
  is missing only the receiver's CURRENT own state.  Its packet is one decision old, and the actor switches phase at almost every step.
- Does not show: that a cheap legal summary of that state exists.

**S4 on the clean closed loop** [L-84]
- Shows: the 4 checkpoints that are positive offline are all worse than the prefix in closed loop.  Pooled Spearman 0.27 over 9 checkpoints.

**Learnability of the label components (v7)** [L-80]
- Shows: g1 is slightly learnable (0.543); the delayed part (0.523) and g3 (0.522) are at chance for the flat critic, on 4 actors.
- Not separated: g1/delayed is a TIME split.  It is not the mechanism split "action effect vs cache maintenance" the user asks for.
  That split was never trained as a target.

**F1 dense labels, DFL loss** [L-66, L-75, L-79]
- Shows: 3.2× states, acquisition rules and a decision loss do not rescue the FLAT legal critic.
- Does not show: anything about structured critics (all used the same architecture, L-82).

**Route 3: pair-shared scheduler critic** [L-87]
- Shows: receiver–sender sharing on the scheduler's inputs moves DEV pair accuracy only from about 0.50–0.52 to 0.52–0.53.

**Route 2: per-agent action value from the agent's own actor input** [L-88, L-89]
- Shows:
  - The value of a single-agent action change IS learnable in part: DEV pair accuracy 0.66 vs 0.60 (actor logits) and 0.50 (random).
  - With the TRUE induced actions, that value ranks message candidates better than any scheduler critic: 0.567, +2.75, 18% of oracle.
  - With the legal response head in place of the true responses it fails: 0.529, abstains.
- Separated for the first time:
  - the value of the action a message induces is learnable with per-agent structure;
  - predicting which delivery induces which action is where the legal scheduler inputs fail.
- Does not show: a legal response signal at the byte cost, or any closed-loop / full-episode effect.  One actor only.
  The input is the post-prefix view.

## 2. Old results

**Fixed-MP2 track**
- M1 (preregistered, held phase): the response bid is +1.85 [+0.95, +2.84], 18% of the oracle.  This is the only
  preregistered legal positive.  Held-phase target: the actor's action is held for 3 decisions.
- M2 (preregistered, closed loop, B4): passes against the retrained control only.  Against the prefix it is −0.68% (n.s.), 4.5% of the oracle.
- TARGET_DIAG: held_3 vs cont_3 capture 49% of the headroom, Spearman 0.41 — the same mismatch one horizon earlier.
- Reading: response information helps on the target it was trained for.  Converting it to closed loop failed even for a FIXED heuristic actor.

**Learned actors, message use (msguse, 11 actors)**

| actor | none | stale (1 step old) | full (every sender fresh) |
|---|---|---|---|
| scratch ×5 | +4.2 … +8.7% (CI > 0) | +0.7 … +3.8% (2/5 CI > 0) | +1.1 … +7.8% |
| BC s1–s4 | +3.0 … +17.5% | −1.0 … +0.9% (all n.s.) | +12.2 … +30.0% (CI > 0) |
| BC s0 | +0.4% | +2.3% | +6.4% |
| mix | −0.9% | **+7.5%** | −1.9% |

- Shows:
  - Prefix-trained actors are HURT by extra information: full communication is worse than the budgeted prefix.
  - They are barely hurt by a uniform one-step delay, especially the BC actors.  The mix actor is the opposite: robust to extra or edited deliveries, fragile to staleness.
  - Under stale, 16–38% of receiver actions change even when waiting does not move on average.
- Does not show: that selectively DROPPING transmissions keeps waiting.  "Stale" delays every message by one step; it is not a selective drop, and it does not measure the future-cache effect of a skipped packet.

**Other old results**
- Delay stress (A4): scratch loses 3.9% / 5.6% at 20 s / 30 s.  Idealised scheduler; a stress test, not the method.
- Same-byte queue bid (S3), SchedNet-style adaptation (S5: +0.4 … +4.8% worse), acquisition (S6): no legal variant helps.
- F5 / F5b (reduced, enumerated panels):
  - The within-family loss is mostly the critic's ranking: +15.2 / +14.2 of +15.6 / +13.6.
  - Coverage outside the family is at least +5.3 / +4.0.
  - Local search from the prefix reaches 85% of the best found.
  - T1's bound was instantiated only with fitted scores (not a certificate).
- E1a / E1b (controlled synthetic calibration): consistent with the needle-class calibration law ON THAT SYNTHETIC CLASS only.

## 3. What the Lean corpus does and does not give (corrected, L-86)
- Directly usable: SafeEdit (τ ≥ 2ε never harms), conditional on an ε never certified for any E3 critic.
- Shape agreement only, not proof for CityFlow:
  - MASTER's necessity dichotomy;
  - `ProxyBlindness`;
  - needle-class calibration;
  - TCC-response;
  - D6 first-order insufficiency.
- For direction (b):
  - `LeanFunctionalCertificateLifetimeV1` (LIFE1–5: gauge triangle, drift composition, bounded update drift, "within certified lifetime", future top-K margin);
  - `SelectiveMaintenanceV1`;
  - `ResidualMaintenanceV2` ("safety conditional on coverage and the stated future-error bound").
  - These are generic TOP-K certificate statements under bounded drift.  They are not about an actor's decision or a receiver cache.
  - The analogous statement (an action is invariant while the accumulated input drift stays under the logit margin divided by a Lipschitz constant, over the certificate's lifetime) is NOT in the corpus.  It would be a new, small module.

## 4. The two directions

**(a) Structured value learning**
- For: L-88 and L-89.
  - The value of an induced action change is learnable per agent.
  - With true responses, it ranks candidates better than every scheduler critic, without scheduler-level training.
- Against: L-87 (sharing on the scheduler's inputs alone does not help) and L-89 (the legal response prediction fails).
  - The bottleneck is the response.  L-83 names what is missing: the receiver's current state.
- Smallest decisive next step:
  - Train a response model from a RECEIVER-computable signal, e.g. the receiver's own margin and its runner-up p2, carried in the existing bid, together with the scheduler's content-change features.
  - Re-run L-89 with it: does the "legal response × Q̂" score approach 0.567 / +2.75?
  - Note: the receiver-computed bid must use the PRE-transmission view.  Generating that needs a probe v3 that saves the pre-transmission x.

**(b) Certificates to cut transmission while keeping decisions**
- For:
  - The environment is deterministic.  If every receiver's action is unchanged at every step, the trajectory, and so waiting, is IDENTICAL.  A zero-loss byte saving is therefore exactly checkable.
  - msguse shows actions and waiting are fairly insensitive to one-step staleness for BC and some scratch actors.
- Against, and the traps:
  - (i) Bytes: the protocol is ONE broadcast stream.  Bytes fall only when a packet leaves the stream: tail truncation, PAYLOAD_B × |T| in `profile_cost`.  A packet may be dropped only if the decisions of EVERY receiver that decodes it are preserved.
  - (ii) Future cache: "the current action is unchanged" is not enough.  The skipped packet leaves an older copy in the caches for later steps.  The certificate must hold against the PREFIX trajectory's caches over its lifetime (the user's point).
  - (iii) 16–38% of actions change under a uniform one-step delay, so certified savings may be small.
- Smallest decisive next step, an oracle diagnostic with simulator access (upper bound, not a method):
  - Record the prefix trajectory's actions.
  - Re-run the episode, each step greedily truncating the stream tail when the resulting actions of ALL receivers equal the recorded prefix actions at this step AND at the next L steps (checked by simulation).
  - Report the bytes saved at IDENTICAL waiting, and how often the future-cache check vetoes a drop that the current-step check allows.
  - If the achievable zero-loss saving is small, (b) closes cheaply.  If it is large, the legal certificate (sender drift × Lipschitz bound < receiver margin, over the lifetime) is the method to build, with a new Lean lemma.

## 5. Not to be claimed
- That legal information cannot suffice (not proved; L-86).
- That the headroom is "not communication" (L-81 covers single-agent changes on one actor at a 3-step scale).
- That any offline gain transfers to closed loop (L-84).
- That the delayed part is unlearnable in general (only the flat critic was tested on it).
