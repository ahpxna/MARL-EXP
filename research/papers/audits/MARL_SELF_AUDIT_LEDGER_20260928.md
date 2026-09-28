# MARL E3 — self-audit ledger (started 28/09/2026 13:05)

This ledger is the working record of the worker's self-audit of its OWN E3 code, Lean and documents
(AGENTS.md result-to-algorithm audit). It is append-only: an entry is never deleted.
- An entry that turns out not to be a defect is marked **WITHDRAWN**, with the reason.
- A repeat of an earlier defect is marked **DUP of L-xx**.
- It does not replace `MARL_CURRENT_CLAIMS_20260928.md`, which is the current claim map, and it does
  not edit ROADMAP / OPEN_MATH / THEOREM_MAP.

**Types**
- **BUG**: the implementation contradicts its own specification or theorem.
- **OVERCLAIM**: text says more than the evidence.
- **STALE**: text contradicts newer results.
- **PROV**: provenance gap.
- **STAT**: missing uncertainty or sensitivity.
- **RISK**: a latent failure that has not occurred yet.
- **OK**: inspected, no defect.

**Status values**
- **open**
- **fixing** (what is running is named)
- **fixed** (where)
- **WITHDRAWN**
- **DUP**

**Cost to fix, in tokens**
- **H**: a rewrite or a long read.
- **M**: a new script or version.
- **L**: a line edit.

## Read-through coverage

| file group | read line by line? |
|---|---|
| bridge v1 / v2, paired_eval, queue_side, diag_v2, acquisition v1, selector v5 diff | yes, before this ledger (13:00) |
| everything else in the list at the bottom | pending, see the entries below as they are read |

## Entries

| id | file:line | type | finding | affected artifact / claim | cost | status |
|---|---|---|---|---|---|---|
| L-01 | scripts/MARL_e3_bridge_panel.py:95 (`range(1, 8)`), :60 | BUG | ScoreLocal (LeanMarlEstimatedRevisionV1) quantifies over EVERY context A, including the empty set. v1 evaluated only 1 ≤ \|A\| ≤ 7, so the reported η* is a LOWER bound on the Lean constant. The docstring "over ALL contexts" is false | `e3_bridge_20260928`; claim T1; E3_INTERIM §F5 | M | fixing: `MARL_e3_bridge_panel_v2.py` (A = {} included), runs `e3_bridge_v2_{scratch_s3,bc_s3}_20260928` |
| L-02 | bridge_panel.py:109 | BUG | hTop was read at ONE minimiser of the Chebyshev LP. The LP optimum is not unique, so "hTop false 16/16" was not certified | same | M | fixing (v2: second LP η_top = min η subject to ScoreLocal ∧ hTop; hTop satisfiable at the optimum iff η_top = η*) |
| L-03 | bridge_panel.py:115 | BUG | "T1 bound" = 2η*(d−R)₊ is not an instance of `score_frontier`, which needs ScoreLocal AND hTop at the SAME w. The valid instance is 2η_top(d−R)₊ ≥ the reported number, so v1 understated the bound. The direction of the reading ("the bound is loose") is unchanged | same; claim T1 row "T1 bound mean 6.62" | M | fixing (v2 reports both, and asserts `score_frontier` on the data) |
| L-04 | bridge_panel.py:108 | BUG (minor) | d = \|P \ A*\| for one arbitrary argmax A*; with ties the tightest valid choice is the minimum over optimal k-sets | same | M | fixing (v2 `d_min`) |
| L-05 | E3_INTERIM:293, CLAIMS S8 | STAT | F2-A "privileged-only − legal = +2.12 [+0.10, +4.49]" is significant only with the episode bootstrap. Clustered by traffic seed (8 seeds, both loads together, handoff F1.3), the CI is [−0.21, +4.56] on scratch s3. On BC s3 it stays positive: [+1.11, +4.68]. Source: `scripts/MARL_e3_paired_eval.py`, which reproduces the recorded episode CIs exactly | claim S8 | L | open |
| L-06 | work/p13_conjectures/LeanMarlSafeEditV1.lean docstring (`argmax_harm_sharp`) | OVERCLAIM (docstring) | "so an edit threshold below 2ε can harm" is not shown by the witness, which is a tie at estimated gain 0 and covers only the threshold τ < 0 with a strict rule. The paper text (line 347) says "an argmax ... can lose 2ε", which IS what the witness shows | Lean docstring only | M | open: add `threshold_sharp` (every τ < 2ε admits a harmful edit) and re-gate |
| L-07 | paper_marl.tex:39–42 (TODOPAR) | STALE | "The headline claim depends on the learned-actor experiments (E3), which do not exist yet" | draft | L | open |
| L-08 | paper_marl.tex:370 | STALE | "the T1 bridge to traffic is open (a one-swap fit bounds η only from below)": F5 now exists (and is being corrected, L-01..04) | draft | L | open (after bridge v2) |
| L-09 | paper_marl.tex:334–356 | STALE (incomplete) | the E3 section reports no F2-A/F2-B/F3/F4/F5 results | draft | H | open |
| L-10 | lane B (`RUN_marl_e3_resume_v2.sh` → `MARL_e3_continuation_labels_v2.py`, BC s4 labels) | RISK | v2 crashes with FileExistsError on its scenarios dir if the watchdog restarts it (fixed in v3, not used by this lane) | BC s4 labels | L | open: check the lane state |
| L-11 | E3_INTERIM:227–228 | OK (superseded) | "the safe rule never edits here, because 2ε ≈ 26" is superseded in the same log at 12:25 (lines 275–280). The log is historical; the correction is recorded | — | — | WITHDRAWN as a defect |
| L-12 | dense labels, `labels.partial_*.jsonl.gz` | PROV | the resumed lines of the dense round came from producer runs whose manifests never existed (killed or stalled runs). Which version (v2 before 11:45, v3 after) wrote which partial file is recorded only in the logs and the file times. Handoff F1.1 asks for this to be preserved | F1 dense round | L | open: write the per-file provenance table |
| L-13 | scripts/MARL_e3_queue_side.py:53 (`env._build_view`) | OK | `_build_view` (envs/external/cityflow_budgeted.py:472) only reads the sensor and the cache (no state change), and the replay self-check on order and K guards against divergence | queue bid data | — | WITHDRAWN (no defect) |
| L-14 | F2-B, `selectors_v5` both actors | result | legal multi-class head − legal binary head: −0.60 / +0.03 (scratch s3), +0.41 / −0.97 (BC s3), all n.s.; privileged − multi +2.1 to +3.8, CI > 0 under both bootstraps. `f2b_paired_dev.json` per actor | claim S8 / F2 | L | open: record in E3_INTERIM and CLAIMS |
| L-15 | scripts/MARL_e3_closed_loop.py:63 (inherited by v2, v3) | RISK | runtime τ parsing is `-inf if tau is None else tau`: a v3+ checkpoint stores '+inf'/'-inf' STRINGS, so deploying any v3/v4/v5 selector in closed loop would crash or compare a float with a string. No v3+ selector has been run in closed loop so far (all closed-loop rows are v1/v2 selectors). Also: no runtime path for qbid, resp_multi or priv_joint (priv is never deployable) | any closed loop or final test with v3+ selectors (F6) | M | open: closed loop v4 (τ strings, qbid from the receivers' own view, multi head) before F6 |
| L-16 | MARL_e3_delay(_v2).py:103, MARL_e3_message_use.py:86, fig3_v4 / e3_frontier `boot` | STAT | bootstrap over EPISODES only; each traffic seed contributes two episodes (loads 8 and 16), so a traffic-seed cluster sensitivity (handoff F1.3) is missing for A2, A4 and the closed-loop rows | claims A2, A4, S1 (closed loop) | M | open: recompute from rows.json with seed clusters (read-only) |
| L-17 | scripts/RUN_marl_e3_ablation.sh:27 → MARL_make_fig3_v4.py:104 | BUG (caption) | the E3 ablation figures `<actor>/figures/fig3_ablation.caption.txt` say "frozen MP2 actor on every method" and explain methods with MP2 wording; the caption text is hard-coded for the MP2 track. Not used in the paper (the paper's F3 is the MP2 figure fig3v4_b4test) | E3 figure captions | L | open: record; any E3 figure for the paper goes through a new version with an actor label |
| L-18 | MARL_e3_delay_v2.py:75–79 | OK (weak check) | the causality assertion can fail only if an env view carried a payload measured after step t − d (the delayed dict is built from the view history), so it checks the env, not the delay logic. The delay logic itself is checked at d = 0 by the encoding and MP2 identities | claim A4 | — | WITHDRAWN as a defect; wording: "causality assertion on the env's payload times" |
| L-19 | MARL_e3_acquisition_v2.py:54 | OK | checked in all 18 manifests: no state is short of the budget (min pool 78 singleton, 149 others); every strategy labelled exactly 24 candidates per training state (18,432 per run) | claim S6 | — | WITHDRAWN (no defect) |
| L-20 | MARL_e3_actor_train_mix.py:66–70 | OK | "uniform over the feasible B1 candidates by rejection" is exact (the first feasible element of a uniform permutation is uniform over the feasible set); the family contains the prefix, so the mix branch picks the prefix with probability ≈ 1/180 | PROTOCOL_E3_MIXACTOR | — | WITHDRAWN (no defect) |
| L-21 | MARL_e3_continuation_labels.py:95, :106 (all versions) | OK (design fact) | candidates are drawn from one rng per episode, in snapshot order, so the DENSE round (snaps 4..22) draws DIFFERENT candidate families at the original snapshots (10, 16, 22) than the original round did. "Same state intersection" therefore means the same (episode, t), not the same candidates; both arms of F1 must be evaluated on ONE label file | F1 design | — | noted (F1 plan below) |
| L-22 | RUN_marl_e3_dense.sh:22 → RUN_marl_e3_ablation.sh | RISK (method) | the dense round auto-runs the v2 ablation (τ grid without +∞, v2 job edit_rate) and a closed loop. The F1 decision must instead compare the SAME v3 trainer on dense vs original labels, evaluated on one label file (L-21) with `MARL_e3_paired_eval.py`; the auto-run v2 ablation is recorded but not the F1 endpoint | F1 | M | open: `RUN_marl_e3_dense_f1.sh` after the dense labels complete |
| L-23 | RUN_marl_e3_resume_v3.sh:6 | STALE (comment) | the comment says "labels: v2 producer"; the script runs v3 | — | L | open (comment only; the script is used by a running lane, so it is NOT edited now) |
| L-24 | MARL_e3_selector_train_v2.py `head_metrics` | OK (minor) | head accuracy includes the prefix rows (target always 0), which inflates accuracy; the reported recall (0.006 → 0.15) is unaffected | claim S2 | — | noted |
| L-25 | PROTOCOL_E3_PILOT §1 and PROTOCOL_E3_SCRATCH ("actor seeds 0, 1, 2") vs `e3_run_seeds34_20260928`, `e3_scratch_seeds34_20260928` | PROV (protocol deviation) | seeds 3 and 4 of both recipes were launched at 00:49 (chain.log; the same protocol hash), BEFORE any E3 result, but no amendment adds them to the seed lists. The only gated scratch actor so far is seed 3, so S1–S8 rest on a seed that the protocol text does not list. No selection on outcome is possible (launched before results), but it must be declared, with every seed reported | claims A1–A4, S1–S8 | L | open: a dated amendment note in a NEW file (the protocols are hash-checked by running chains and are not edited) |
| L-26 | paper_marl.tex:145–146 | OVERCLAIM | "from the learned-actor round on, the grid contains 'always keep the prefix'" is false for every closed-loop and frontier result on learned actors (v1/v2 selectors, τ grid without +∞); only the v3+ diagnostics have it | draft Methodology | L | open |
| L-27 | paper_marl.tex:318–324 | STALE | "max pressure has 12% to 23% more total waiting": with BC s1 (+9.5%) and BC s4 (+11.9%) finished, the range is 9.5–23.1% (msguse reports). The warm-started recipe's G1 "varies by seed (+0.4% pilot; +5.7% another)": now BC s1 +11.3%, s3 +5.7%, s4 +17.5% pass; 3 of 4 BC seeds pass, the pilot fails | draft E3 | L | open |
| L-28 | paper_marl.tex:330 | OVERCLAIM | "over two gated actors": BC s3 passes G1 on its own, but the BC recipe is gated on its pilot seed s0, which failed; only scratch s3 is gated | draft E3 (SchedNet) | L | open |
| L-29 | paper_marl.tex:351–354 | OVERCLAIM (context) + STALE | "With larger caps the selectors of the warm-started actor are 2–4% worse" omits that the BC chain is recorded under a failed gate; the NOTE cites `e3_selector_diag_scratch_s3.json` (v1 diagnostic, invalid ties) instead of `e3_selector_diag_v2_scratch_s3.json` | draft E3 | L | open |
| L-30 | paper_marl.tex:4–5 (header comment) | STALE | "nothing is a learned-actor result yet" | draft source comment | L | open |
| L-31 | PROTOCOL_E3_ABLATION Amendment 1 vs RUN_marl_e3_dense.sh | PROV (deviation) + correction of L-22 | the amendment registers directories `labels_dense_*`, "the same producer (MARL_e3_continuation_labels.py)" and the v2 ablation. The implementation uses `<actor>/dense/labels_*`, producers v2 (partials before 11:45) and v3 (the same per-state code path; `e3_labv2_test_*` showed resumed lines identical). Correction to L-22: the auto-run v2 ablation IS the registered analysis. The v3 paired comparison is the handoff's added analysis (+∞ τ), and both are reported | F1 | L | open: declare in the F1 record |
| L-32 | PROTOCOL_E3_DELAY_ACQ B ("the dense round when complete") | pending registered item | acquisition v2 on the dense labels of scratch s3 is registered and not yet run | S6 | M (compute) | open: after the dense labels |
| L-33 | paper_marl.tex §E3 + Limitations | STALE (incomplete), part of L-09 | the delay stress test (A4) is described in Limitations but its result is not reported anywhere in the draft; BC s1/s4 actors are missing | draft | H (with L-09) | open |
| L-34 | F5 v1 vs v2 (partial, 13:09) | consequence of L-02 | on scratch s3, bridge v2 already finds states with η_top = η*, i.e. hTop IS satisfiable at the optimal constant. v1's "hTop false in 16/16" was an artefact of reading one LP minimiser. The T1 row of the claim map and E3_INTERIM §F5 must be corrected from v2 | claim T1; E3_INTERIM:381–399 | L | open: after v2 completes |

## Work ranked by token cost (heaviest first), 13:10
1. **H: manuscript rewrite** — L-07, L-08, L-09, L-26 to L-30, L-33. Abstract TODO, Methodology, E3 section with every development result (competence and G1 for all actors, delay, SchedNet, ablation, diagnostics, F2-A/B, F3, F4, F5 from v2), Limitations. Then compile and visually check the PDF.
2. **M: Lean** — L-06 `threshold_sharp` in LeanMarlSafeEditV1, plus a new smoke gate (compiled in the background first, so it runs during item 1).
3. **M: closed loop v4** — L-15, before F6.
4. **M: seed-cluster recomputation** — L-16 (read-only).
5. **M: F1 runner** — L-22/L-31 (v3 trainer on the dense labels, paired on one label file), prepared now, run when the labels complete.
6. **L: records** — L-05, L-14, L-25, L-12, L-34 in E3_INTERIM / CLAIMS / an amendment note.

## Status update about 13:18 (timestamp corrected at 13:26; first written as 13:25, ahead of the clock)
| id | status |
|---|---|
| L-01..L-04 | **fixed**: `MARL_e3_bridge_panel_v2.py`, runs `e3_bridge_v2_{scratch,bc}_s3_20260928` COMPLETE, self-check PASS. L-01 detail: v1 also omitted the FULL set (\|A\| = 7 contexts), not only the empty set |
| L-34 | **fixed**: v1's "hTop false 16/16" withdrawn. hTop is satisfiable at the optimum in 5/16 per actor. Recorded in E3_INTERIM (13:20), CLAIMS T1 and the paper |
| L-05, L-14 | **fixed**: E3_INTERIM 13:20, CLAIMS S8 |
| L-06 | **fixed**: `threshold_sharp`, `threshold_sharp_positive` added; smoke gate `smokeSafeEdit2_20260928` PASS (7 theorems, standard axioms); cited in the paper |
| L-07, L-08, L-09, L-26 to L-30, L-33 | **fixed** in paper_marl.tex (rewritten E3 section with the new Fig. 4 `fig_e3.pdf`, Limitations, abstract, Methodology, TODOPAR); compiles (tectonic exit 0); pages 8–10 visually checked |
| new | the paper sentence "differences between legal arms are not significant" was itself checked: 1 of 21 pairs per actor IS significant; the text was corrected before compiling |
| L-12 | open. Finding while checking: `dense/labels_dev/labels.partial_0.jsonl.gz` (the v1-produced lines) is TRUNCATED; its gzip stream ends without an end marker (the run was killed). The v2/v3 resume reads complete lines up to the truncation (EOFError caught), so no line is lost silently, but the file is not a complete gzip |
| L-15, L-16, L-22/L-31, L-25 note, L-32 | open |

## Status update 13:26 (second pass over the open items; first written as 13:35, ahead of the clock)
| id | status |
|---|---|
| L-15 | **fixed**: `scripts/MARL_e3_closed_loop_v4.py`. It parses τ strings, supports qbid (from the receivers' own view, as queue_side), the multi-class head and several selector dirs, and refuses priv_joint. Self-checks before any episode: runtime scores equal the trainer path (max diff 0.00e+00 for 12 selectors) and the chosen indices equal the trainer's `dev_chosen` (v3+). Smoke `e3_clv4_smoke_132100`: prefix and sel_bid_resp s0–s2 are IDENTICAL to `cl_v3_direct` (queue, finished, bytes, edits); v3, v4 (qbid) and v5 selectors run |
| L-16 | **fixed**: `scripts/MARL_e3_seed_cluster.py` gives `e3_seed_cluster_20260928.{json,txt}`, 109 endpoints, with episode vs traffic-seed bootstrap. Self-check: the means reproduce the stored reports. Significance changes for 2 endpoints: BC s0 shuffle (+2.13 becomes significant; not a gate quantity) and BC s3 frontier +56 sel_bid (+1.95 becomes n.s.). G1, A1, the scratch s3 closed loop, delay and SchedNet keep their readings |
| L-22, L-31, L-32 | **prepared**: `scripts/RUN_marl_e3_dense_f1.sh`. It runs the v3 trainer on the dense labels (legal_bid_resp, priv_only), a paired eval on (a) the 48 original dev states and (b) the full dense dev panel, then acquisition v2 on dense. It refuses unless every dense label dir is complete; DRY test refused correctly (rc 2). Launch after the dense labels complete; the registered v2 ablation runs by itself from RUN_marl_e3_dense.sh |
| L-12 | **fixed**: `research/marl_budget/E3_PROVENANCE_NOTES_20260928.md` §2 has the per-file producer table (v1 1,170 states in partial_0, truncated gzip; v2 copy; v3 the rest). v3 recomputed the v1 state seed501_load8 t4: IDENTICAL line (166 candidates) |
| L-25 | **fixed** (declared): same file §1; the paper's NOTE and Limitations cite it |
| L-10 | **happened**. BC s4 `labels_train_1` and `labels_train_2` died with FileExistsError under producer v2: the watchdog restarts crashed, and each log shows 3 watchdog lines. **Fixed in flight at 13:25**: both shards were relaunched in place with v3 under the watchdog (resumed 55 and 56 states). Shard 0 is still running under v2 and was not touched. Lane B's resume_v2 will report "a stage failed" when shard 0 ends. The s4 downstream (selectors, closed loop) then needs `RUN_marl_e3_resume_v3.sh e3_run_seeds34_20260928 bc "4"` |
| L-35 (new) | **RISK, same defect as L-10**: lane C (`RUN_marl_e3_resume_v2.sh e3_scratch_seeds34_20260928 scratch 4`) will produce scratch s4's labels with v2 once training ends. Any watchdog restart then crashes. Plan: if it happens, relaunch the dead shards with v3 exactly as for L-10. Lane 2 (`RUN_marl_e3_resume.sh` v1, scratch s0/1/2) has the known pipefail stop after training s0; scratch s0/1/2 go through resume_v3 after lane 2 exits (already planned) |
| L-17 | open (record only): E3 figures from fig3_v4 carry an MP2 caption. The paper now uses `fig_e3.pdf` (own caption), so no paper figure is affected |
| L-23 | open (comment only): the script is used by running lanes and is not edited |

## Entries after the independent post-F5 recheck (13:5x)
| id | file:line | type | finding | affected | cost | status |
|---|---|---|---|---|---|---|
| L-36 | lane C, `e3_scratch_seeds34_20260928/actor_s4` (MARL_e3_actor_train.py has no resume) | RISK (happened) | the scratch s4 actor stalled 3 times: 11:09, 12:23/12:52, and 13:44 at about iteration 1000. Each time the watchdog parked the partial run in `legacy/actor_s4_stalled_*` and **restarted training from iteration 0**, so hours of training were lost. The 13:44 stall came 11 minutes after 12 F5b processes were added (13:33). This is consistent with the CityFlow barrier deadlock under oversubscription, and it is not proven to be the cause. No result is affected (the stalled attempts were never used); the cost is wall time | scratch seed pass rate (F6 needs all seeds) | M | open: a resumable trainer (from ckpt_last + optimizer state) would be a NEW version and a declared deviation; lower load where possible |
| L-37 | tools | OK | `scripts/MARL_e3_watch_episode.py` (CityFlow replays of any actor, including a running training's `ckpt_best.pt` copied read-only; refuses 1301–1316) and `scripts/MARL_e3_dashboard.py` (live progress from the jobs' own logs through symlinks). Not experiment results | — | — | added |

## Independent recheck (MARL_POST_F5_INDEPENDENT_RECHECK_20260928.md) — entries and status at 14:07
(This block was rewritten at 14:08: the first write at 14:07 used an unquoted heredoc, and the shell dropped every
back-quoted name. Nothing was executed, because the scripts are not executable.)

| id | source | type | finding | status |
|---|---|---|---|---|
| L-36 | recheck §1 | OVERCLAIM (my wording) | "hTop satisfiable in 5/16" was written as if the theorem held only there. Precisely: η_top = η* in 5/16; at η_top EVERY state (16/16 per actor) has a valid ScoreLocal + hTop instance. Ratios where the bound is nonzero: 2.8, 3.29, 6, 6.67. The scores are fitted AFTER seeing the full table, so this is a reduced-object numerical instantiation, not a deployable certificate | open: paper, CLAIMS, E3_INTERIM wording |
| L-37 | recheck §1 scope; user point 1 | OVERCLAIM (scope) | F5 varies ONE receiver with the others at the prefix, so it cannot show that a multi-receiver selector's loss is all estimation | **fixing with code**: `scripts/MARL_e3_multireceiver_decomp.py` (F5b). Multi-receiver decomposition on the 48 dev states × 2 actors using the labels' multi-receiver families and the arms' actual choices, plus a multi-receiver rollout local search as a coverage lower bound and an additivity test. Runs `e3_mrdecomp_20260928`, 12 shards |
| L-38 | recheck P1 resume closure; user point 2 | PROV | my L-12 wording "no line is lost silently" was not established by the resume logic (it catches read errors; last duplicate wins; failures=[] reset) | **fixed**: `scripts/MARL_e3_labels_audit.py`, output `e3_labels_audit_v2_20260928.{json,txt}`, 39 label dirs, verdict PASS for every one. Per dir it checks expected keys from the producer args (missing/extraneous), keys lost from partials, duplicate keys in the loader file, canonical-JSON conflicts between copies, mid-stream JSON errors, record semantics (prefix = candidate 0, legal and distinct candidates, bytes == profile_cost, finite values), and every per-state log line of every attempt (no new self-check failure; each final key has a production line, or the dir is a single-attempt run covered by its manifest). Plus the v1→v3 replay (seed501_load8 t4 identical) |
| L-39 | recheck P1 seeds; user point 3 | PROV | the early launch of seeds 3–4 does not rule out later selective reporting | **fixed**: `research/marl_budget/PROTOCOL_DEVIATION_E3_SEEDS_20260928.md` (dated 14:06, not backdated). It has every seed and failed attempt, and 7 binding reporting commitments |
| L-40 | recheck P0 | BUG (my v4) | `closed_loop_v4.parse_tau` accepted NaN (silently always-prefix) and bare 'inf'; no per-step byte parity; no tie / no-feasible tests | **fixed**: `scripts/MARL_e3_closed_loop_v5.py` (v4 kept as an artifact). Strict τ parsing; selftest PASS (7 decision cases, 6 rejected forms); per-step byte parity assertion; dev smoke `e3_clv5_dev_smoke_140422` (seed 501, 10 methods) PASS |
| L-41 | recheck P1 F1 | method | the F1 density comparison must keep SELECT/tuning fixed and report resources | **fixed (prepared)**: `scripts/RUN_marl_e3_dense_f1.sh` v2 adds arms origsel, matched (13 epochs ≈ equal gradient steps) and full; ONE common table each time; label audit gate; diag v2; `f1_resources.json`; acquisition on dense. DRY refused correctly |
| L-42 | user report (scratch s4 hang ×3) | RISK → loss | the trainer has no resume: scratch s4 lost ~1,640 iterations (reached 510 / 137 / 997) and is on its LAST watchdog retry; scratch s0 has 1 retry left | **fixed going forward**: `scripts/MARL_e3_actor_train_resume.py`, full-state atomic checkpoints (this also answers "reading a half-written checkpoint"), in-place resume. Verified BITWISE: original == resume-trainer and uninterrupted == stopped-and-resumed, for scratch and mix (mix test non-vacuous). Replicas s0, s1, s2, s4 launched 14:03:24 in `e3_scratch_rs_20260928`; the run-of-record rule was written before launch |
| L-43 | user point 4 (Q^{π0} bridge) | missing guarantee (optional) | SafeEdit is about the H = 3 value of one step, not the episode return; a policy-improvement bridge would need Q^{π0}(x, S) with a state that includes caches and ages, plus a valid ε(x) | open, OPTIONAL (the user said it is not required); the paper keeps the local scope |
| L-44 | user point 5 | method (F6) | "benefit" may be a pre-registered trade-off (same bytes and lower waiting; non-inferiority within a fixed margin with fewer bytes; less calibration; budget stability). A CI containing 0 is not equivalence | open → part of the F6 freeze |
| L-45 | my own shell use, 14:07 | process | an unquoted heredoc with back-quoted names would execute them as commands. Nothing ran (not executable), but a future note could run a script | noted: quoted heredocs (<<'EOF') for every note from now on |

## Outstanding work — full sweep (handoff F0–F7, recheck P0–P3, this ledger, manuscript TODOs, claim map) at 14:11
**Waiting on running jobs (each has its runner ready).**
1. F1 dense labels. Runner `RUN_marl_e3_dense_f1.sh` (gated on completion and the label audit). The registered v2 ablation starts by itself.
2. F2-C mix actor. Runner `RUN_marl_e3_mix_downstream.sh` (refuses until the mix manifest exists).
3. Scratch s0, s1, s2, s4:
   - replicas in `e3_scratch_rs_20260928`, lane runs for s0 and s4;
   - downstream via `RUN_marl_e3_resume_v3.sh e3_scratch_rs_20260928 scratch "0 1 2 4"`, ONLY after the replica manifests exist (otherwise it would retrain with the old trainer);
   - the run-of-record comparison with the lane runs.
4. BC s4. Shard 0 still runs on v2; shards 1 and 2 run on v3. After ALL shards complete, start `RUN_marl_e3_resume_v3.sh e3_run_seeds34_20260928 bc "4"` (not earlier, or there would be a second writer).
5. BC s1/s2 and the lane-D chain: s1 is at the selector stage; s2 comes after.
6. F5b multi-receiver decomposition: report, then CLAIMS, E3_INTERIM and the paper.

**Not started, required before submission.**
7. F6 freeze manifest. Contents:
   - actor seeds and gate rule; checkpoints and hashes;
   - runtime `MARL_e3_closed_loop_v5.py`, thresholds, candidate generator;
   - baselines (prefix, direct no-bid, response-bid, R1, SchedNet-style, same-byte queue bid, oracle diagnostic);
   - absolute resource accounting;
   - primary endpoint TYPE (superiority, or non-inferiority with a fixed margin: L-44);
   - aggregation over actor × traffic seeds, guardrails.
   Only then run 1301–1316 once.
8. Frontier and shift for the from-scratch actors (manuscript TODO). This needs a gated scratch actor with selectors on caps +28/+56/+84/+140.
9. Manuscript:
   - F5b paragraph; L-36 wording (5/16 at η* vs 16/16 at η_top; post-hoc fitted);
   - dense, mix and seed results when they exist;
   - the final figures after F6; remove the TODOs.
   - Venue/track and author/affiliation are the AUTHOR's decision (not blocking).

**Optional / not blocking.**
10. L-43 Q^{π0} policy-improvement bridge (Lean) — the user said it is not required.
11. L-17 (MP2 caption on E3 ablation figures, not used in the paper) and L-23 (a stale comment in a running script): record only.
12. Commit: nothing has been committed since 3ae456b. Commit only when the user asks.

**Done in this sweep's session.** L-01..L-16, L-25, L-34, L-36..L-42 fixed as recorded above. The manuscript bibliography TODOs are
filled and verified: M2I2 = Sun, He, Ji, Zang, Li, Wang, Wang, AAAI 2026 (ojs.aaai.org article 39764); MUTE = Zuo, Huang, Li, Zhang,
Khan, Qiu, arXiv:2607.03473, preprint.

| L-37 (status 14:24) | **fixed with code (result)**: F5b multi-receiver decomposition. Scratch s3 47/48 states (the last reruns after a verified CityFlow deadlock: `sample` shows both threads in _pthread_cond_wait), BC s3 48/48. Estimation dominates (+15.5 / +13.7), but coverage (≥ +4.5 / +3.7) and R1 geometry (+2.6 / +2.5) are nonzero. The paper, abstract, Limitations and CLAIMS S9 now say so. Self-consistency: the BC legal arm (−1.31 [−2.32, −0.20]) and the family headroom (12.33) equal the paired-eval and oracle values |

## Status 14:43 — lanes B and C ended (harness task brfxdbr8p)
| id | status |
|---|---|
| L-35 | **happened**: the lane-C scratch s4 run hung a 4th time (14:42:54, at iteration ~560 of its last attempt), and the watchdog retries are exhausted. The lane run is dead: ~2,200 iterations lost in total, all parked in `legacy/actor_s4_stalled_*`. By the pre-declared rule (`e3_scratch_rs_20260928/RUN_OF_RECORD_RULE.md`) the replica `e3_scratch_rs_20260928/actor_s4` is now the only s4 run; its trace was identical to the lane run while both lived |
| L-10 | **happened again**: BC s4 shard 0 (the last v2 writer) also died with FileExistsError on a restart. Checked that no writer was left, then relaunched it in place with v3 at 14:43:49. All three BC s4 shards now run on v3. The downstream (`RUN_marl_e3_resume_v3.sh e3_run_seeds34_20260928 bc "4"`) waits until all three have manifests |
| new | lane B ran the v2 ablation for BC s1 (recorded, not read, because the BC gate failed). Every variant is WORSE than the prefix: sel_nobid +2.45% [+0.94, +4.03], sel_bid +3.89%, sel_resp +4.13%, sel_bid_resp +2.52% [+0.84, +4.21]. It also re-ran the BC s3 ablation report. BC s2 was skipped (not trained yet; lane D trains it) |

| L-42 (status 15:01) | **resume verified in production**: replica s0 hung at 14:31:55 and resumed at iteration 140 with full state. Its trace stays IDENTICAL to the lane-2 run over 438 common iterations, including those after the resume. BC s2 finished: select 1467, G1 PASS (+3.0% [+0.9, +5.2], change 0.24), MP2 +12.4%. The BC recipe is 4/5 seeds passing, with the pilot s0 failing |

| L-37 (final 15:15) | F5b complete, 48/48 × 2. Final numbers are in the paper, CLAIMS S9 and E3_INTERIM. Self-consistency: legal realised −0.19 / −1.31 and family headroom 15.44 / 12.33 equal the paired-eval and oracle values |

| L-46 (15:32) | loss (the same defect as L-42) | the lane-2 scratch s0 run hung at iteration ~1943 of 2000 (last ckpt it 1940, select 1411) and was killed at 15:25:36. The old trainer has no resume, so it restarted FROM SCRATCH on its last watchdog retry (attempt 3). Lost: ~1,940 iterations, parked in `legacy/actor_s0_stalled_2_20260928_152536`. The resumable replica `e3_scratch_rs_20260928/actor_s0` (iteration ~1063, trace identical to the lane run) will almost surely complete first. By the pre-declared rule it is then the run of record |

| F2-C (15:36) | the mix actor completed (lane run, no hang; best select 1352), so it is the run of record by the pre-declared rule. The replica `e3_mixactor_rs_20260928` (launched 15:32:25) is redundant: it will be compared at completion or can be stopped by the user. Downstream launched 15:36:21 (log `e3_mix_downstream.log`; protocol hash 018ae5ef… recorded) |
