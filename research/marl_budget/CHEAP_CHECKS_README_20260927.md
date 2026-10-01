# Cheap checks — what is ready to run

Two executable screening stages are ready: global-broadcast oracle headroom, then supervised selectors on held-out traffic episodes. Neither stage trains a MARL actor. Fixed actor = two-step max-pressure; labels hold the joint phase action for H decision boundaries. These tests can reject a weak mechanism/evaluator on the tested panel; they cannot establish final learned-MARL or long-run traffic superiority.

## Fast mechanism screen, no neural training

```bash
cd /Users/phanan/cig-amf-main
CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 external_envs/runtime/bin/python -u scripts/MARL_cheap_screen.py --profile screen --out "research/marl_budget/cheap_screen_$(date +%Y%m%d_%H%M%S)"
```

24 snapshots: 3x3 grid, two loads, three traffic seeds, four snapshots/episode. All 512 subsets per snapshot; each subset changes information for EVERY receiver under the same sender set. Every interior budget is evaluated. Oracle computations are cached only when joint actions are identical; this is valid for the explicitly held-phase continuation used here.

Outputs: manifest.json, summary.json, tables.jsonl.gz. Each record includes public scheduler context, all subset values, all joint actions, prefix/repair/optimal gaps, real access-log checks and live collection-step bytes. Zero gaps and negative learned-repair gains are never filtered.

This small screen has too few training contexts to judge neural sample efficiency. The training script rejects it by default; --allow-tiny is for wiring checks only.

## Main cheap pilot (recommended once headroom is worth investigating)

```bash
cd /Users/phanan/cig-amf-main
bash scripts/RUN_marl_cheap_pilot.sh
```

This writes a new timestamped directory and runs sequentially:

1. 192 tables: 3x3 grid, two loads, eight traffic seeds, 12 snapshots/episode. Train = seeds 11–14, validation = 21–22, test = 31–32. Both loads for a seed stay in the same split. There are 96/48/48 train/validation/test contexts; all budgets use the same context split.
2. Small score, set-value, and direct budget-conditioned networks; CPU, one Torch thread, 150 epochs, initialization seeds 0/1/2. All methods receive the same full training tables. Validation selects checkpoints; test is evaluated only after training/checkpoint selection. No claim about acquisition efficiency from this dataset.

The shared actor is frozen. `features` contains only previously transmitted packet contents, presence/age, and public time. Current own observations belong to actors, not to the public scheduler. Neither fresh hidden payloads nor oracle singleton gains enter neural runtime inputs. The network can therefore fail to predict full-state oracle repairs; this is a meaningful limitation to measure.

The direct baseline receives budget k explicitly. Its training loss is expected true training-table value under a distribution on legal k-subsets, avoiding arbitrary tie-broken target labels. At inference it chooses top-k of its budget-conditioned logits. Repair enumerates the whole legal family and uses the learned evaluator. No greedy coverage guarantee is assumed.

Results: models/report.json, models/seed_*_test.json, models/seed_*.pt. Raw records permit regrouping by k, episode and load. Headline pilot means are per-episode means of regret across contexts/budgets; state count is not treated as independent replication. Three neural initialization seeds are NOT three MARL actor-training seeds.

Comparators: cached-queue prefix; learned-score prefix; learned R1/R2 repair; direct budget network; unrestricted search using the same critic; oracle R1 repair; oracle per-budget subset. Oracle choices are diagnostic references only.

## Interpret in this order

1. Read cached_queue_headroom and geometry_true_singletons separately. True singleton scores are an oracle reference, not deployed importance estimates.
2. Read raw regret as well as gain over learned prefix. `mean_episode_gain` may be negative and is intentionally preserved. A low baseline gap can leave nothing to repair.
3. Compare learned repair with the direct budget network and critic unrestricted search. Beating a weak fixed ranking alone is insufficient.
4. Check each k and each load/seed; aggregate tables are an overview, not evidence of uniform improvement.
5. Full-table labels, tiny neural models and short-horizon returns limit conclusions. Failure on a small panel is not a theorem of impossibility. Success is a reason to run the learned-actor/online experiment next, not to claim the whole MARL paper validated.

## What remains outside these commands

No learned actor; no online rollout of learned selectors; no closed-loop long-horizon improvement; no SchedNet adaptation; no traffic-time consumption for compute delay; no hardware latency superiority; no formal neural confidence bounds; no calibration-acquisition advantage. For these, use the submission-critical-path document. Do not label this pilot as E3.

## Checks performed during implementation

13 unit tests: exact repair enumeration, network-wide packet and replacement accounting, fresh-payload non-interference with positive control, counterfactual/live actor inputs, oracle guard mutation, clone/restore consistency, known headroom, data hash/split checks, test-label non-interference, and negative-gain retention. A real CityFlow 2x2 smoke and a two-epoch pilot also completed. Small checks verify code wiring; their scores are not scientific outcomes.

```bash
cd /Users/phanan/cig-amf-main
PYTHONDONTWRITEBYTECODE=1 CIG_EXTERNAL_RUNTIME_ACTIVE=1 external_envs/runtime/bin/python -m unittest tests.test_marl_broadcast_screen tests.test_marl_revision_selector tests.test_marl_cheap_pilot -v
```

The historical receiver-budget scripts/artifacts are untouched. New collectors refuse to overwrite output directories; the pilot requires COMPLETE metadata and matching raw-table hash. Do not edit producer files during a run; the collector and trainer check source drift before marking completion.
