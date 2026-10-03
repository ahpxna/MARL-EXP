# PROTOCOL — E3 age emulation (receiver-side garbling) vs relabel: a direct test of H1 / reviewer G2
Written 03/10/2026 02:5x EDT (wake 1), BEFORE any panel run.  Script scripts/MARL_e3_age_emulation_eval.py, launcher
scripts/RUN_marl_e3_age_emulation.sh, report scripts/MARL_e3_age_emulation_report.py.

## Question
H1 (FAILURE_SYNTHESIS_20261002 F1) says an input edit repairs a frozen receiver iff it keeps the conditional law of what the
receiver infers given the edited input; reviewer G2 says a repair must keep payload, age and target coupled.  All E3 input
edits so far RELABELLED (age remap, onefresh, time projection, clip) and failed; the RI testbed's TRUE emulation (an actually
older sample with its true age) worked (L-263, AR3).  E3 never ran the true-emulation edit.  Here: a relayCK1 receiver (trained
at constant capacity 1) on the upgraded channels; before the actor reads its merged view, entries fresher than its training
support are replaced by the receiver's OWN earlier copy of the same sender with the copy's TRUE age (EMU), or — control — keep
the fresh payload and only show the older age (LAB, the same substitution decisions).  The protocol state is unchanged
(only the actor input differs), as in the clip / remap evaluations.

## Design
* Support = rank-wise age floors: sort the relayed entries of a view by age; floor[r] = 5 % quantile (pre-set, not tuned) of
  the r-th smallest age over the receiver's own training-channel episodes (calibration seeds 301–332 × headways 8/16, plain
  relay; relayCK1: K = 1; relayCage / relay6Cage: iid).  Smoke floors: 3×3 relayCK1_s0 [0, 1, …, 7], 4×4 [0, 1, …, 9, 11].
* Panel 5101–5164 × headways 8/16 (new; not used by any earlier protocol), 64 × 2 = 128 episodes per cell.
* 4×4 (grid relay wrapper, nearest8): seeds 0–9; relayCK1_st at K ∈ {1, iid, 2, 3}; relayCage_st at iid (control); Z_s on
  the panel.  3×3: seeds 0–4; relayCK1_st at K ∈ {1, iid, 2, 3}; relay6Cage_st at iid; Z_s.
* One process per cell runs PLAIN, EMU and LAB on the same episodes (paired).  Gain vs Z = −(ΣR/ΣZ − 1)·100 per seed;
  bootstrap over seeds and traffic seeds (as in MARL_e3_g4_train_match_report.py).
* Self-checks: zero floors ⇒ EMU = LAB = PLAIN exactly (first episode of every cell); every substituted copy is older than the
  current copy and carries its true age (assert); source hashes frozen during a run; checkpoint sha in floors and manifest.

## Predictions (fixed now)
* EM1 (repair at the upgrade, 4×4, relayCK1, iid): gain(EMU) − gain(PLAIN) > 0, bootstrap lower bound > 0, ≥ 7/10 seeds > 0.
* EM2 (H1 contrast, 4×4, iid): gain(EMU) − gain(LAB) > 0, lower bound > 0, ≥ 7/10 seeds > 0.
* EM3 (magnitude, 4×4): gain(EMU@iid) − gain(PLAIN@iid) ≥ ½ [gain(PLAIN@K1) − gain(PLAIN@iid)] (half of the hazard recovered).
* EM4 (near-identity where the receiver is in support): |gain(EMU) − gain(PLAIN)| ≤ 0.3 points for relayCK1 at K = 1 and for
  the Cage receiver at iid, both networks.
* EM5 (3×3 replication, seeds 0–4): the signs of EM1 and EM2 in ≥ 4/5 seeds.
* Reported, no prediction: K = 2, 3; LAB − PLAIN; substitution and missing rates; the same on 3×3.
Kill rules: EM2 failing on both networks ⇒ H1 (coupled edits repair, relabels do not) is NOT supported in E3.  EM2 holding with
EM1 failing ⇒ coupling matters but garbling back into the per-rank support is not a repair (joint-configuration or closed-loop
effects remain) — reported as such, no repair claim.
Smoke disclosure (non-panel seeds 9001–9002, seen before writing this): 3×3 relayCK1_s0 iid 2 episodes PLAIN 1786 / 1734, EMU
1854 / 1650, LAB 1710 / 1697; 4×4 1 episode PLAIN 1841, EMU 2112, LAB 2023 (not evidence; predictions are H1's and unchanged).

## Novelty and scope
Garbling to an older experiment is classical (Blackwell; constant-delay playout buffers in networked control, Luck & Ray 1990);
the RI minimal emulation is ours (L-263).  The contribution is the test of H1 inside learned closed-loop MARL receivers.
What this is NOT: no real controller logs, no actual J2735 traces, no independently developed vehicle stack, no real city
cross-version data — CityFlow simulation with our own trained receivers only.

## Amendment 1 (03:0x EDT 03/10, after the pipeline smoke, BEFORE any panel run)
The first pipeline smoke (non-panel seeds 9001–9002; archived legacy/e3_age_emulation_smoke_pipe_rankfloors_*) showed a design
flaw on 4×4: rank-wise floors are computed over ALL held entries (up to 15) while the 4×4 actor reads only its 8 nearest slots,
so near (decision-relevant) entries were pushed to ages their slots never had in training (EMU −12.9 vs PLAIN at iid, 1 seed).
Added PER-SLOT floors (floor[i][j] = 5 % quantile of sender j's age in receiver i's training views) as the PRIMARY modes EMU /
LAB; the registered rank-wise version stays as EMUR / LABR (reported, same predictions applied as secondary).  EM1–EM5 now
refer to the per-slot modes; nothing else changes.  Second smoke (same non-panel seeds, seen): per-slot floors 3×3 relayCK1_s0
mean 0.07 / max 1 (K1's marginal support covers every slot — 3×3 support is JOINT), 4×4 mean 3.73 / max 8; 4×4 iid EMU −2.34
vs PLAIN, EMU − LAB +2.85; 3×3 iid EMU +1.33 vs PLAIN, EMU − LAB +2.98 (4 episodes each; not evidence).  Expected reading if
these hold: EM2 (coupling) yes, EM1 (repair) no on 4×4 — the registered "coupling matters, marginal garbling is not a repair"
outcome, consistent with joint support (test C, L-272).  No further design change before the panel.
