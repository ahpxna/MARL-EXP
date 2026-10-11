# One-hour wake duties — night of 04/10/2026 (standing order from the user, 01:3x EDT)

**User request** (verbatim, abridged): "đặt báo thức cho đêm nay giống hqua (mỗi 1 tiếng, lần đầu dậy là 1 tiếng 10 phút sau)" → corrected to "1h8m". Make the audit verification first. Then at each wake:
- "tập trung hoàn thành tất cả những nhiệm vụ còn treo, thử đồng huấn luyện 2 quần thể đèn xe, cho mọi policy đèn ghép với mọi policy xe, vân vân";
- "làm theo hướng dẫn dưới, tham khảo và cãi những chỗ nó nói sai sau khi research";
- the overall picture and destination are as in the review: two learned populations (lights, cars). I may change direction based on research toward what is most novel, most practical and above all free of collision, but the multi-population MARL context must be kept.

**Wake schedule** (extended by the user 01:4x: "làm cho đến 11h sáng"): 02:41 (first), then 03:41, 04:41, 05:41, 06:41, 07:41, 08:41, 09:41, 10:41.

**User 01:4x, the loop for every wake** (verbatim): "lần báo thức này ko dc fetch agents, chỉ dc tự research và tìm tòi, ráng brainstorm dựa trên những kết quả thực nghiệm, r lại chạy thí nghiẹm, có kết quả thì lại đọc r phân tích và báo cáo, r lại brainstorm, r lại chay thí nghiệm,... r lại research,... pretty much việc đêm nay của m mỗi lần wake up là v, làm cho đến 11h sáng".
Each wake is one cycle: BRAINSTORM from the latest results → (protocol) RUN → READ + ANALYSE + REPORT → RESEARCH → brainstorm again.

**Mechanism** (as on 03/10):
- One background alarm `caffeinate -i -t <s>; date '+WAKE-ALARM-n fired …'`, re-armed as the **first** action of each wake, to the exact next target.
- Exactly one alarm pending.
- Not CronCreate.
- The first two firings are verified and reported.

**Subagents.** NONE: the user's message did not say "fetch". The 2-subagent allowance of 03/10 was specific to that night.

## Duties at every wake (in order)

- **W0 — Re-arm + log.** Re-arm, run `date`, add a line to the log below. Check `df -g` and swap; the guard needs at least 15 GB free.
- **W1 — Pending tasks** (finish, do not merely check). Current list, updated each wake:
  - **E3 track:**
    - E9c panel → `MARL_e3_e9_report.py`, then an addendum and ledger row.
    - E8 → `report_e8`.
    - G3: frozen panels → write `CITY_g3_oos_weighting.py` → smoke → run → report.
    - E12: `MARL_e3_emu_coverage_eval.py` + `MARL_e3_e12_report.py` → smoke → queue.
    - E14: RUN / QUEUE / report → smoke → queue, at low priority.
    - Lean `LeanMarlPacketEmulatorV1` (E12-a) → compile → smoke gate, then check that prints equal the theorem count.
    - Update FRAMING_LEGACY_VIEW with E7 / E13 / E9.
    - P5 figures.
  - **Two-population track** (TWO_POPULATION_AUDIT_VERIFY_20261004 §5):
    - B0 inventory;
    - B1 cross-play 4×4 + controls;
    - B1b H-crawl (crawl-aware queue sensing, no retraining);
    - B2 L-RLH_t for t = 1..3, then the (L0,F0) … (L1,F1) matrix;
    - B3 alternating co-training, plus the light-reward = time-loss ablation (equal budget);
    - B4 pilot of a regression-constrained light update vs mixture / cap / fine-tune / rollback / co-training.

    Each step goes protocol → smoke → queue. Two-population runs get CPU priority over E14.
- **W2 — Progress.** Every queue and process: progress, FAIL / retries, ETA from measured rates. Read every finished report against its registered predictions, following the AGENTS.md audit rules.
- **W3 — Literature, deep reading.** Method, experiments and discussion of CoTV, SGMRL, FastAP, FCP / other-play / ZSC, MACPO / MAPPO-L, and partner-shift work in TSC. Update the collision table. Argue with the review where the evidence says it is wrong.
- **W4 — Hypotheses.** Verify on our own assets: H-crawl, two-sided incompatibility, susceptibility tied to light vs fleet vs pair.
- **W5 — Report.** Short Vietnamese report to the user: what finished, what the numbers say, and what runs next.

## Wake log
| n | target | fired | notes |
|---|---|---|---|
| 0 | — | 01:33 armed | alarm 1 → 02:41 (caffeinate -t 4080, PID 21983); audit verified (TWO_POPULATION_AUDIT_VERIFY_20261004.md); G6 NO-GO; E7 P-a/b/c SUPPORTED; E13 report written |
| 1 | 02:41 | 02:42:01 | re-armed → 03:41 (3527 s) |
| 2 | 03:41 | 03:42:02 | Re-armed → 04:41 (3531 s, task bq45y7scb). Disk 25 GB free; swap 1.2 GB. **B1 panel** 102/102, but parity FAIL 156/160. Cause: hash-order jitter in `CarRL.step` (set iteration, PYTHONHASHSEED); it also affects Q7/Q7b. Addendum A1: h0 panel + jitter envelope; `CITY_xplay_report_h0.py`. **B3 protocol** `PROTOCOL_CITY_COTRAIN_20261004.md` (novelty: CoTV / HONEST-CAV have no cross-play). `CITY_cotrain.py` smoke OK; training queue launched 03:51 (15 runs). ALT gridlocks in its first block (note N1). `CITY_xplay2.py` parity bit-identical; 650-config queue launched 03:53 (phase 2 waits for training). `CITY_cotrain_report.py` written. |
| 2b | (user message 04:0x) | — | Three new reviews verified line by line: `TWO_POPULATION_NEW_DIRECTION_VERIFY_20261004.md` (24 claims; 2 corrected: parity resolved and larger than they thought; E13 NI actually fails). V1 commanded-vs-realized run → C-13 (the idle penalty is avoided by command, 76–99.7 %). `functional.tex:484` fixed (g ≥ 0). Full program + ETA `TWO_POPULATION_EXPERIMENT_PROGRAM_20261004.md` (2×2: who upgrades × where repaired). Next: F0 (CarRL v2 + F1 training) and V3 once training lanes free; B4F / B3-X reports. |
| 3 | 04:41 | 04:42:04 | Re-armed → 05:41 (task bs2pgq08e). **Results:** E12 all SUPPORTED (L-330); B4F FB-1 / FB-3 SUPPORTED, FB-2 not, clip ✗ (C-14); B3-X C-1..C-3 not supported, learned fleets worse than humans (C-15). **User 04:4x:** read related repos, write code for everything, queue sequentially because the machine is overloaded. Done: OMP=1 bit-identical; sequential spool `RUN_spool_20261004.sh`; `CITY_eval2.py` (unified evaluator, replay identity fixed twice by its own self-check), `CITY_fleet_upgrade.py` (CarRLv2), `CITY_dcada_tune.py` (DC-Ada port, sigma amended to 0.03 before running), reports written before data; jobs 010–090 queued (ETA ~07:15). Repos read: DC-Ada (MIT), RESCO (GPL-3), sumo-rl (MIT), CoTV (MIT). Clones not made (permission). |
| 3b | (user 05:1x and 05:2x audits) | — | Amendment W3 applied (eval3, reporter v2, splits, NI, always-SUMO identity, phase-boundary handoff after setProgram bug). C-16 (L4 all registered SUPPORTED), C-17 (no fleet beats SUMO's driver model), C-18, C-19. B6 added as the decisive next step; v2 / v3 trace checks; spool reordered (021 running 05:31). RESCO cloned (permission). |
| 4 | 05:41 | 05:42:05 | Re-armed → 06:41 (task b2pwhabpw). Disk 17 GB (E3 `scenarios` dirs: E14 5.3 GB, w2 6.9 GB; regenerable; plan: lossless archive to legacy/ if free disk < 16 GB). Done since wake 3: E14 report (L-331, NOT SUPPORTED); Lean E12-a `LeanMarlPacketEmulatorV1` (compile clean, 10 audited theorems, smoke gate running); FRAMING §5; Paper C odd limitation (gated module, hash match) and FUNCTIONAL rebuilt; v2 trace 021 PASS; Cologne8 prepared for G4. Spool: 034 (v3 trace) running. |
| 5 | 06:41 | 06:42:06 | (work continued from wake 4: B6-N, the C-22 sentinel bug, v6, the B6-R / B6-I queue). **Not re-armed:** the session hit its usage limit after 06:4x. |
| 6–7 | 07:41, 08:41 | MISSED | Usage-limit gap 06:4x → 08:42. The spool kept running (all jobs done by 07:49). |
| 8 | (resume) | 08:42:08 | Re-armed → 09:41 (task b19m7hfi2). Read every finished job (C-23): B6-R v6 negative under B6-1 but with a time-benefit trade-off; 041–045 exploratory results. Registered B6-T (post hoc criterion, confirmation only on new seeds 213 / 313 and traffic 400–409) → job 046 running 08:45. Prepared Branch-P job 047 (eval5 with ACT support) and its reporter. Disk 29 GB, swap 0.6 GB. |
| 8b | (working, 09:18) | — | B6-T NOT CONFIRMED (C-26). B6-Z (C-25, C-27): release ≡ SUMO; residual δ = 0 jams the network (`getSpeedWithoutTraCI` capped by `setSpeed`); σ = 0 SUMO is −5.2 s/veh and every learned fleet is slower. B6-S (C-28): σ 0.2–0.4 dominate always-SUMO, and no learned fleet is beyond the σ-family. Registered and queued: B6-H horizon (049b, v7 trainer, trace check PASS) and B6-SL (049c, σ-fleet under frozen RL-H). Legacy-view draft v2 compiled (adds EMU − ALLNEW −0.59). Memory: project_city_fleet_comparators. |
| 9 | 09:41 | 09:42:06 | Re-armed → 10:41 (task bnhgk50xy). Disk 29 GB, swap 0.64 GB, load 4.8. Results since 8b: B6-H (C-29: R5h_t0 passes B6-1 and is beyond the σ-family; t1 fails; horizon effect not established); B6-SL (C-30: σ 0.3 fleet upgrade compatible with frozen RL-H, interaction −0.16). Registered B6-R5 (replicate R5h on 4 new seeds, fresh traffic 410–419, generated locally with the verified randomTrips config); job 050r running. |
| 9b | (working, 10:20) | — | B6-R5 NOT CONFIRMED (C-31), step 4 closed. Positive fleet-upgrade results: T4 confirmed on VALIDATION (C-32), ACC super-additive (C-33), generalizes to RL-C50 / RL-J (C-34). Cologne8: the grid4 light recipe is worse than FT; T4 / T5 inconclusive (C-35). G4-L2 (480-episode cologne8 light) running. Night report §6 (summary + decisions) written. Claim table `TWO_POPULATION_CLAIM_TABLE_20261004.md`. |
| 10 | 10:41 | 10:42:16 | Last wake (loop ends at 11:00, so no re-arm). Since 9b: G4-L2 (C-36): the cologne8 light is worse at 480 episodes (+15.10 vs FT), so G4 stops. Spool empty; 060 / 070 / 095 still on hold; no simulation running; disk 29 GB. Night report §6 holds the summary and the decisions for the user. |
