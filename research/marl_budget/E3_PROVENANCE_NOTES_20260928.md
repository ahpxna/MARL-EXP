# E3 provenance notes (28/09/2026, 13:26; self-audit L-12 and L-25)

- A declaration file. It changes no protocol: the protocols are hash-checked by running chains and
  stay unedited.
- It edits no ledger.

## 1. Actor seeds 3 and 4 (L-25)

**What the protocols say.** PROTOCOL_E3_PILOT §1 and PROTOCOL_E3_SCRATCH list actor seeds 0, 1, 2.

**What was run.** Seeds 3 and 4 of both recipes were also run:
- `e3_run_seeds34_20260928` (BC + MAPPO);
- `e3_scratch_seeds34_20260928` (scratch).

**When they started.** The chain logs show both chains starting at 00:49 on 28/09, under the SAME
protocol hashes:
- `a552be06…` (pilot);
- `19289fcc…` (scratch).

At that time no E3 label, selector or closed-loop result existed; only training curves did. So no seed
could have been chosen by its outcome.

**Why they started.** The user asked for more overnight runs. No amendment was written to add the seeds.

**Consequences, declared here.**
- The only gated from-scratch actor so far is seed 3.
- Every learned-actor selector result (S1–S8) rests on seeds outside the protocols' seed lists.
- All actor seeds are reported, with the gate pass rates:
  - BC recipe, gated on pilot s0: s0 fails G1; s1, s3 and s4 pass on their own; s2 is pending.
  - Scratch recipe, gated per seed: s3 passes; s0, s1, s2 and s4 are pending.

**Final protocol (F6).** It must list every actor seed and the gate rule in advance. A result on a
gated subgroup stays conditional on the gate.

## 2. Dense-label producer provenance (L-12)

Directory: `e3_scratch_seeds34_20260928/actor_s3/dense/labels_{train_0..5, select, dev}`.

| file | written | producer | content |
|---|---|---|---|
| `labels.partial_0.jsonl.gz` | 11:35–11:36 | **v1** `MARL_e3_continuation_labels.py` (run killed by pkill at 11:37) | 1,170 states in total: dev 225, select 225, train 92 / 151 / 113 / 122 / 9 / 233. The gzip stream is TRUNCATED; every complete line up to the cut is readable |
| `labels.partial_1.jsonl.gz` | 11:40 | **v2**, which crashed with FileExistsError on its scenarios dir | a verbatim copy of partial_0's complete lines (same counts); complete gzip |
| `labels.partial_2/3.jsonl.gz` | 12:05–12:52 | **v3**, parked by watchdog restarts | the resumed copies plus new v3 states; truncated at each kill |
| `labels.jsonl.gz` (current) | from 11:42 | **v3** | the union: every resumed line copied verbatim, then the new states |

Resume logic, v2 and v3 alike:
- every COMPLETE line of every partial file is kept;
- lines are deduplicated by (episode, t);
- the files are renamed, never deleted.

Checked on 28/09 at 12:55: each current file has no duplicate (episode, t).

**Determinism check (13:24).** The v3 producer recomputed the v1-produced state (seed501_load8, t = 4,
development) from scratch in a fresh directory (`--snaps 4 --limit 1`; t = 4 is the first snapshot, so the
candidate rng is aligned). The recomputed line is IDENTICAL to the v1 line: all 166 candidates, with their
continuation values, joint actions, bids and bytes. The per-state code path agrees with the v2 test
`e3_labv2_test_{full,resume}_113900`.

**What this does NOT show.** Every other v1 line was not recomputed; that would mean redoing the round.
The dense round's final manifest will carry only v3's source hashes. The mixed provenance of its lines is
declared here and must be cited with any dense-label result.

## 3. Candidate families at the original snapshots (L-21)

Candidates are drawn from one rng per episode, in snapshot order. The dense round (snapshots 4–22)
therefore draws DIFFERENT candidate families at the original snapshots (10, 16, 22) than the original
round did.

The F1 comparison (`scripts/RUN_marl_e3_dense_f1.sh`) evaluates both training sets on ONE label file at
a time:
- the original development states;
- the full dense development panel.
