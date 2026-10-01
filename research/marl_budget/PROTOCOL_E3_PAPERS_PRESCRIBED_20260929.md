# E3 experiments prescribed by the ten papers (DEVELOPMENT protocol, 29/09/2026, written 20:1x EDT before any result below)

Why this exists: the old papers predicted the mechanisms that sank the E3 selectors.  The user asked (19:5x, 20:0x) for
experiments DESIGNED around those predictions, paper by paper, run now.  The ledger is
`research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md` (L-117 onward); the reading notes are
`research/papers/audits/MARL_OLD_PAPERS_REREAD_20260929.md`.  Every rule below is a design lesson taken from a paper,
not a transferred theorem (L-86).

## Common settings (all arms)
- Actor recipe: the scratch MAPPO recipe (2000 iterations, 8 episodes/iteration, lr 3e-4, entropy 0.01, hidden 128,
  eval every 20, 2 threads), seed 0.
  - Trainer `scripts/MARL_e3_actor_train_delivery_v6.py`: the resume trainer with only `episode()` replaced.
  - Identity: `--delivery prefix` reproduces the resume trainer, select 4089.1875 after 2 iterations.
- Checkpoint: `ckpt_best.pt` on SELECT (401–408).  SELECT is optimistic (L-111), so it is NEVER the endpoint.
- Endpoint panel: 128 episodes, seeds 901–964 × headways 8/16, `scripts/MARL_e3_delivery_eval_v5.py`.
  - The actor is run under its own delivery rule and capacity process.
  - This panel was already used today, so it is development data, not a test.
- Bytes: accounted by the shared cost function.
  - For receiver-side decode rules (rxq, rxold), the honest cost is the prefix STREAM.  The receiver chooses inside
    what is broadcast, so no per-receiver description is needed.  The report prints both.
- References on the same 128 episodes:
  - the co-trained NONE actor of the same architecture: flat none_s0 (seed 1 as a replicate), set_none_s0;
  - maxq (the best heuristic, 0 B, L-115/L-116);
  - the prefix system (5 scratch prefix actors).

## Pre-stated success criterion for a communication claim (per arm)
- PRIMARY: paired per-episode waiting ratio of the arm vs the SAME-ARCHITECTURE none actor.
  - Bootstrap over traffic seeds, both headways together, 4000 resamples.
  - The upper 95 % bound must be < 0, at stream bytes ≤ the prefix's (188.7 B/step).
- An arm that passes is read as a development signal only after seed 1 replicates it; that replicate is queued after
  the first pass.
- Anything else is reported as a negative or a tie, as measured.

## Paper by paper: the lesson, the predicted E3 pitfall, the prescription, the arm, and what would falsify it
- **MASTER** (a missing query type gives value 0, silently).
  - Pitfall: the scheduler cannot see the receiver's current state; the reference controller fails silently.
  - Prescription: put the decode choice at the receiver, and audit every reference.
  - Arms: `rxq_s0` (flat) and `set_rxq_s0` (set actor).  The receiver decodes, from the stream, its physical
    neighbours first by the waiting in its OWN cache.  References re-audited (L-114/L-116).
  - Falsified if receiver-side decoding does not beat the none actor.
- **Paper B** (the query class is the lever; obstructions).
  - Pitfall: scheduler-side ranking at chance.
  - Prescription: a receiver-side query class.
  - The same rxq arms, plus the legal proxy of (b) (L-98).
- **Paper A** (a frozen surrogate starves the decision cells; repair costs a β fraction of surrogate value).
  - Pitfall: actors trained only on the prefix support.
  - Prescription: β-mixture training.
  - Arm: `mixrand_s0` (random order with probability 0.5).  Evaluated under the prefix AND a random order: does β buy
    robustness at a small prefix cost?
  - Falsified if it is worse than the prefix actor under the prefix, and no better elsewhere.
- **Paper C** (a marginal band removes the order information; one exchange suffices when weights are known).
  - Pitfall: the fresh flag leaks the priority (L-90).
  - Prescription: uniform order marginals.
  - Arms: `rand_s0` (flat) and `set_rand_s0` (set), random order at every step.
  - Falsified if they remain worse than none.
- **STRUCTURAL** and **FUNCTIONAL** (signed budgets serve no single order; proxies fail when their reference moves).
  - Pitfall: k_i redrawn every step, so the delivered set never stays the same.
  - Prescription: a consistent capacity.
  - Arms, each against none and against the prefix actor under the same process:
    - `fixcap_s0` (flat) and `set_fixcap_s0` (set): capacities fixed per episode;
    - `highcap_s0`: capacities in 5..7.
  - Falsified if consistency does not change the comm-vs-none sign.
- **ADAPTIVE** (tracking and apportionment bound deficits).
  - Pitfall: unbounded staleness of undelivered pairs.
  - Prescription: a refresh rule with bounded age.
  - Arms: `rxold_s0` and `set_rxold_s0`.  The receiver decodes its oldest cached copies first, neighbours first.
- **UNIFIED** (the support term; a phase in which measuring nothing is optimal) and DRMAC / Message-Dropout (receiver
  confounders; dropout robustness).
  - Pitfall: comm actors worse than none; irrelevant dimensions hurt.
  - Prescription: the none control first, then a structured, masked receiver.
  - Arms: none_s0 / none_s1 / set_none_s0 (controls); nbrmask_s0/_s1, set_prefix_s0, set_nbr_s0 (running or done).
- **SUPPORT** (pairwise safety is not whole-fibre safety), **D6** (a 2δ margin; fitted weights are not derivations),
  **QUERY** (the measurement sets the order).
  - No new arm now.
    - SUPPORT and D6 constrain how results are CERTIFIED: whole-fibre checks, no fitted-weight certificates.
    - QUERY's payload change needs a protocol change and is listed as not run.

## Not run (stated so that nothing is silently dropped)
- A payload change (QUERY).
- The actor seeing its own capacity k_i (paper C's "knowing the budget"): it needs an adapter change.
- A learned (policy-gradient) receiver decode policy: rxq and rxold are the fixed-rule versions.
- Seed-1 replicates of any passing arm: queued only after a pass.
