# Pre-specified PILOT 2: do local-fibre obstructions exist, and is the teacher message-need N_s an obstruction measure?

Written 01/10/2026 10:5x EDT, BEFORE any run of the probe below (user 10:3x).  Evidence class: PILOT with pre-stated kill
rules (development panel, two seeds); a pass licenses a confirmatory test, it is not itself the confirmation.
Why: N_s (PROTOCOL_E3_COMM_VALUE_PREDICTOR) asks whether the teacher's OWN action changes when fresh senders are removed
from ONE realised state.  Paper B's obstruction needs ALTERNATIVE worlds consistent with the receiver's local view
(EXTERNAL_ANALYSIS_VERIFICATION_20261001.md, items 28/29 and caveat 7).

## System and states
- Executed system: relay6Cage_st_s<s> closed loop, age-first order, capacity `low`, relay v2 merge, 3 B codebook (the V-D10
  system, whose rollouts equal the satrot rows byte for byte).  Teacher set_full_s<s> (diagnostic only).
- Seeds s = 1 (highest N_s, 0.456) and s = 8 (lowest, 0.118).
- Receiver-states: 64 per seed, one per episode, episodes seed901 … seed932 × load 8 / 16 (development panel); for each
  episode t ~ U{4, …, 21} and receiver i ~ U{0, …, 8} from numpy default_rng(20261001 + s).
- Information set of the receiver = its LOCAL observation (lane_vehicles, lane_waiting, own_phase, own_phase_elapsed,
  decision_step): exactly the zero-byte student's input.

## Alternative worlds (a declared sub-family of the local fibre)
For every remote agent j ≠ i, every valid phase φ ≠ j's executed action at step t − δ, δ ∈ {1, 2}: replay the episode
deterministically from t = 0 with j forced to φ at t − δ (everything else the closed loop) up to step t.  The world is
ACCEPTED iff i's local observation at t is identical (arrays exactly equal) to the original world's.  At most 11
accepted alternatives are kept, in the deterministic order (δ, j round-robin, φ); F = {original} ∪ kept.
Because F is a SUBSET of the true fibre, ∩_{w∈F} A(w) ⊇ ∩ over the true fibre: an obstruction found on F is real, and
every rate below is a LOWER bound of the true-fibre rate.

## Values and acceptable sets (simulator rollouts; the oracle never chooses an executed action)
V(w, a) = −Σ_{u=t}^{25} queue_u with receiver i forced to action a at step t in world w and the closed loop otherwise, to
the end of the episode (3-step labels correlate only 0.39–0.61 with full-episode values, ledger audit).
A_ε(w) = {a valid : V(w, a) ≥ max_b V(w, b) − ε·|V(w, a_exec(w))|}, ε ∈ {0.001, 0.005, 0.02}; PRIMARY ε = 0.005.
Obstruction at the state: O = [∩_{w∈F} A_ε(w) = ∅].

## Teacher message-need proxy at the original world (the N_s definition)
need_cache = [teacher argmax on the zero-fresh, CACHE-base view ∉ A_0.25(teacher full-view logits)].
Secondary: need_empty with the view stripped to the local observation only.

## Kill rules and prediction (fixed now)
- K1: pooled obstruction rate at the primary ε < 5 % ⇒ STOP the whole-fibre / obstruction framing for E3 (keep only the
  empirical N_s law).
- K2: Cohen's κ between O and need_cache (pooled, primary ε) < 0.1 ⇒ N_s is reported as a teacher-sensitivity metric,
  not an obstruction measure.
- K3: obstruction rate at ε = 0.001 more than 3 × the rate at ε = 0.02 (or positive at 0.001 and zero at 0.02) ⇒ the
  acceptable sets are unstable; the definition needs revision before any confirmatory use.
- P (direction, reported with a state bootstrap, 4000 draws, seed 0): obstruction rate(s1) > obstruction rate(s8).
- GO for a confirmatory whole-fibre test (more seeds, second network) only if none of K1–K3 triggers.
- Secondary (reported, no rule): per obstruction pair, whether some sender's RAW payload at t splits it and whether its
  3 B quantised block does (representability); the hitting number of the pairwise obstructions by senders; fibre sizes;
  the share of states where the teacher's full-view action is in A_ε (teacher quality); agreement of O with need_empty.

## Self-checks (the probe refuses to write a result otherwise)
- Replaying the original world without forcing reproduces the satrot row's episode waiting exactly.
- Forcing i to its executed action at t reproduces the unforced value exactly.
- Every accepted alternative has a byte-identical local observation at t.

## Not changed after this file
States, seeds, alternative family, values, ε grid and primary, K1–K3, P.  Probe `scripts/MARL_e3_whole_fibre_probe.py`
and report `scripts/MARL_e3_whole_fibre_report.py` are written before the runs.
