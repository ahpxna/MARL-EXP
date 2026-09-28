# PROTOCOL E3-DELAY and E3-ACQUISITION — the two missing step-5 experiments (28/09/2026, 12:20)

- Written before either experiment has any result.
- No ledger is edited.
- Scope: PROTOCOL_HETERO_v0 with Amendment 1, and the E3 actors.

## A. Communication delay acting on traffic (`scripts/MARL_e3_delay.py`)

**Model.**
- Payloads broadcast at decision step t reach their receivers at step t + d, with
  d ∈ {0, 1, 2, 3} steps (0, 10, 20, 30 s).
- At step t a receiver acts on the cache it had at step t − d, aged by d × 10 s. Its own sensor
  stays fresh.
- The scheduler (the committed cached-queue prefix, R = 0) and the byte accounting are unchanged.
- Delay acts on the simulator through the actions it changes.

**Methods.**
- Frozen learned actors that passed G1/G2: scratch s3 and BC s3.
- Frozen MP2 under the same delay, computed from the delayed payloads through `LegalView`.

**Self-checks (the run refuses to report if either fails).**
- At d = 0, the delayed encoding equals `CommAdapter.encode(view, 'actual')` at every step.
- At d = 0, the delayed MP2 action equals `mp2_action(view)` at every step.

**Panel.** Pilot panel 901–916 × headways 8, 16.

**Endpoints, paired by episode.**
- Σ waiting at d against d = 0 for each method.
- Learned actor against MP2 at each d.

**Reading.** Descriptive. It replaces the zero-delay-only scope. It is not an end-to-end
network-latency claim: there is no packet loss, jitter or bandwidth queue.

## B. Label-acquisition ablation on traffic (`scripts/MARL_e3_acquisition.py`)

**Budget.** B = 24 labelled candidates per training state for every strategy, plus the prefix.
That is about 14% of the candidate family, so all strategies spend the same number of simulator
rollouts.

**Strategies.** Candidates are drawn per state from the stored continuation labels. This is
equivalent to labelling only those candidates.
- `singleton`: uniformly among single-receiver one-swaps only (importance-style acquisition).
- `uniform`: uniformly among all candidates.
- `targeted`: without replacement, with probability proportional to
  Σ over the changed receivers of 1/(1 + bid gap), using legal bid information. This focuses on
  receivers whose decision is near a tie.
- `full`: all candidates (reference; a larger budget).

**Evaluator.** `MARL_e3_selector_train_v2.py` variant `sel_bid_resp`, unchanged.
- Train split subsampled by the strategy.
- Select and development splits full, so tuning is equal across strategies.
- Init seeds 0–2; subsampling seed = init seed.

**Labels and actors.** scratch s3's labels (the original round; the dense round when complete) and
BC s3's labels.

**Endpoints.**
- Realised gain on development (full candidate sets), against the oracle.
- Within-state Spearman correlation and the empirical ε, from `MARL_e3_selector_diag.py`.

**Reading.** Development. This is the traffic counterpart of E1's controlled acquisition ablation
(targeted ≡ uniform there, a negative control). A strategy "helps" only if its development gain
exceeds uniform's across all three seeds.
