# One-hour wake duties — night of 04→05/10/2026 (standing order from the user, 20:18 EDT)

**User request** (verbatim): "đặt báo thức giống đêm qua đi, mục tiêu của đêm nay là hoàn thành M3 và M4. Giờ làm lần đầu, lần thứ 2 là 1 tiếng 33p nữa"

**Wake schedule:**
- Wake 1: now (20:18).
- Wake 2: 21:51.
- Then hourly: 22:51, 23:51, 00:51, … 10:51. The end time is the worker's assumption, matching last night; the user may stop it.

**Mechanism** (as 03/10 and 04/10):
- One background alarm `caffeinate -i -t <s>; date '+WAKE-ALARM-n fired …'`, re-armed as the FIRST action of each wake, to the exact next target.
- Exactly one alarm pending. Not CronCreate.
- The first two firings are verified and reported.

**Subagents.** NONE: the user's message did not say "fetch".

**Goal tonight: complete M3 and M4** (milestones of `TWO_POPULATION_PAPER_FINISH_LINE_20261004.md`). "Complete" means a registered result is reached: a confirmed method, or a confirmed negative with the reason named. A win is never manufactured by moving gates.

## Rules (standing)

- Protocol (with predictions) before every run; smoke and self-checks before the panel; `python -u`; PYTHONHASHSEED=0; OMP_NUM_THREADS=1.
- No edits to running or frozen scripts; new versions only; hashes recorded.
- A ledger row for every result (`research/city_sim/CITY_LEDGER_20261002.md`).
- Vietnamese report at each wake.
- Before writing any mechanistic claim, look for a counterexample in the existing data (the lesson of C-69).
- Never kill processes without the user's instruction. Disk guard 15 GB; watch swap.

## Duties at every wake (in order)

- **W0 — Re-arm + log.** Re-arm the alarm, run `date`, add a line to the log below, check `df -g` and swap.
- **W1 — Read finished runs, apply the registered gates, write ledger rows.**
- **W2 — M3 track:**
  - F1 (adapted fleet) DEV gate → confirmation if it passes.
  - Clean decomposition A2.
  - M3′ candidate from the D-dir specification (receiver-triggered precision commitment): protocol → checks → DEV screen → freeze → confirmation on 510–529 with the 5 new lights.
- **W3 — M4 track:**
  - Choose and build the second, independent setting.
  - A working learned-light baseline (it must beat FT / ACT there).
  - SPaT fleet (the R8 rule, R9 search, optionally R10).
  - The M2 matrix there, then the M3 winner (if any) tested there.
- **W4 — Research:** literature for M3′ / M4 novelty and collisions; argue with the reviews where the evidence disagrees.
- **W5 — Short Vietnamese report:** what finished, the verdicts, what is running, the next wake.

## Wake log

| # | Target | Fired | Notes |
|---|---|---|---|
| 1 | 20:18 (now) | 20:19:08 | Alarm 2 armed (bvjvtt4r1, caffeinate 5 506 s → 21:51). Disk 20 GB; swap 9.4 / 10.2 GB used, high (about 10 live viewers and the dashboard hold memory; the user is asked before stopping them). Running: F1 chain (§0 locked q 0.1, infeasible; F1 training 8 runs, about ep 25 / 200), A2 shadow (12 / 40).  Wake-1 work: M4 — arterial4x4 rejected by its registered rule; spider built (M4-A2 / A3); stage-1 RLK training + automatic DEV eval launched (C-74). |
|  | (wake 1, continued) | 20:39 | A2 clean decomposition done (C-75: E0-physical gridlock was an input artifact, 0 / 60 under shadow). M4-1 PASS on spider (C-76: RLK − FT −57 s/veh). M4 2a PASS (C-77: rule −9.2 % fuel vs σ*). M3′ RPC registered, P1 / P2 PASS, smoke bad (+10 % fuel), DEV screen running. F1 at about ep 115 / 200. R9 spider search running. |
|  | (wake 1, continued) | 21:18 | C-79: M3′ RPC DEV tier 1 FAIL, stopped. Bare-rule reference under RL-H: +3.28 %. C-80: M4 2b pilot FAIL (R9 search not better than the rule on spider; confirmation not evaluated). C-81: M4 stage 3 (M2 matrix on spider) replicates M2 (labelled LOST without harm; naive LOST with harm); correction: the rule's TL parity vs σ\* fails marginally on fresh traffic. F1-A1 (post-DEV confirmation of F1-scratch on 5 new lights × 530–549) registered; KA-1…4 PASS; training running, report about 21:52. Swap 9.8 / 10.2 GB, disk 20 GB. |
|  | (wake 1, continued) | 21:39 | C-82 M4 4a NEGATIVE REPLICATED on spider (+6.68 %; the fleet contribution ≈ 0, so the reason is not named). C-83 NetInfo audit note. C-84 provider yellow-branch bug (−1 s, demonstrated; F1 labels updated, no mid-run change). M3-NC registered and running (checks PASS). 4b registered and prepared (KK-1 / KK-3 PASS), conditional on F1-A1. |
| 2 | 21:51 | 21:52:01 | Alarm 3 armed (bzi520wi6 → 22:51) at 21:52:15. Disk 18 GB (it was 20; the run directories are only MBs, so the cause is elsewhere; guard 15). Swap 9.8 / 10.2 GB. Results since wake 1: C-79…C-85. F1-A1 NOT CONFIRMED (agent TL upper +0.55). M4 stage 3 and 4a done; 4b not run (registered condition). M3-NC panel running. **First firing verified: on time to the minute (21:52:01 vs 21:51 target, 1 min late).** |
|  | (wake 2) | 21:59 | Correction: disk was 20 GB again at 21:53 (the 18 GB reading was transient). C-86: M3-NC NEGATIVE CONFIRMED for both arms, reason named; M3 = confirmed negative; M4 complete on spider. Nothing running except alarm 3. |
| 3 | 22:51 | 22:52:00 | Alarm 4 armed (b7p2b0t00 → 23:51) at 22:52:15. Disk 23 GB; swap 10.2 / 11.3 GB (a swap file was added). Since wake 2: the user's review (errata C-88; method-paper destination kept); M4 stage 3 complete launched (C-89 DEV selection: all q infeasible); F1-B registered, B0 PASS (offline and online), chain running (B1). **Second firing verified: on time to the minute (+1 min).** |

## Standing order UPDATE (23:00, user, verbatim)
"cập nhật là trong đêm nay, đến 12h trưa, nhiệm vụ là tiếp tục tìm phương pháp, thay vì chỉ cố vượt một gate chạy các diagnostic những nơi toả ra dấu hiệu có tín hiệu gì đó từ các kết quả chạy dc, kiểm nguyên nhân các thất bại, Kiểm có cơ hội lợi ròng hay không,... vân vân, làm thí nghiệm, làm dirty work thí nghiệm để tìm ra đường thoát và thành công thật sự với M3"

- **Wakes** continue hourly at :51 until **11:51** (the last before noon).
- **Each wake:** diagnostics where results show a signal; failure-cause checks; net-benefit opportunity checks.
- A signal that survives becomes a NEW registered candidate (DEV, then confirmation on fresh data). No gate is moved.
- The user's audits `M3_M4_FINAL_AND_F1B_REVIEW_20261004.md` and `M3_FAILURE_CAUSES_AND_METHOD_PATH_20261004.md` set the order:
  1. M3′-D (RPC H1 / H2).
  2. The H3 continuation opportunity check, which gates any commitment-selection learner.
  3. A net-benefit selector only if an opportunity exists.
  4. F1-B as a bounded parallel reference.
|  | (wake 3, cont.) | 23:05 | User 22:4x–23:0x: (1) review → errata C-88, method destination kept; (2) 'Thử hết M3 chưa?' → stage 3 complete launched, F1-B registered + B0 PASS + chain; (3) review 2 → M3′-D 2×2 registered, smoke, launched; H3 registered; (4) run to 12:00 searching for a method; (5) 'machine heavy, queue it' → no new launches, H3 queued in queue_night_20261005 (spool waits on the 3 chains). Load 37.8. |
|  | (wake 4) | 23:55 | Alarm killed by the session restart; wake 4 taken at 23:52, alarm 5 armed (b6t89ozjf → 00:51). Results: C-91 (M4 stage 3 complete), C-92 (M3′-D runner bug; rerun queued 005), C-93 (F1-B B1). The user's mandatory hypothesis list (N1–N8 + RPC / H3) → plan `M3_NIGHT_PLAN_20261005.md`. Load 19, swap 10.3 / 11.3 GB, disk 23 GB. |
| 5 | 00:51 | 00:52:00 (taken 00:48; firing +1 min, on time) | Alarm 6 armed early (bdh874wp0 → 01:51) at 00:48. Disk 23 GB; swap 10.2 / 11.3 GB; load 11–13. User request this hour: re-read the ChatGPT audits → all 27 read; `CHATGPT_AUDITS_CROSSCHECK_20261005.md`. Results: C-95 M3′-D (H1 / H2 SUPPORTED, best cell still +3.06 %); C-96 H3 (YES = max-of-noise); C-97 N1 REJECTED; C-98 N5 / N6 REJECTED OOS (SNR ≈ 0.2); C-99 **N2: −3.3 % fuel vs R but agent TL +2.1…+2.3**; C-100 N2M (hidden demand SUPPORTED; time cost fleet-intrinsic in open loop); C-101 N7 SUPPORTED (existing data); C-102 X2 (N2 loses the exact yellow answers; N4 SELECT frontier ≈ 0.8 s per 1 % fuel). Queue: 033 N4 DEV running; 032a1 GQ, 032a X3, 032b N8 (KN8-1 caught a SPaT error → fixed), 034 N3 pending. |

## Standing order UPDATE (01:39, 05/10, user)

"tắt bớt viewer cho máy chạy nhanh hơn đi, bật cyb thôi. từ giờ tới mấy lượt wake up sau m vẫn make sure là toàn bộ giả thiết đã dc test/đã dc viết thí nghiệm để test và đã bỏ vào queue. và lưu vào nhắc lúc 4:52 research anyway và gom hết những giả thiết đã test dc nguyên đêm để xem có collision ko, gather citation, tìm thêm các thứ trong phần methodology của các paper khác xem có thể giúp gì mình ko? cái nào có thể giúp có lối thoát? xem cả những paper liên quan tới phần toán mà thuần toán á, mấy paper mà publish trên mấy journal toán học á. Sau khi research thì đọc lại toàn bộ results và ledger, gom lại tất cả để chuẩn bị viết bài nếu đã đầy đủ assets, nếu chưa thì để dành token để thiết kế thí ngghiệm bỏ vào queue tiếp hoặc viết lean, hoặc chứng minh gì đó,..."

- Viewers: only n-HYB (8782) kept ("cyb" read as HYB; swap if the user meant another).
- **Each wake:** hypothesis-coverage diff; every untested item gets an experiment written and queued.
- **04:52 RESEARCH (regardless of TSI):**
  1. Collision check of every hypothesis tested tonight.
  2. Citations.
  3. Methodology mining (escape routes).
  4. Pure-math journal papers.
- **Then:** re-read results and the ledger → a paper-assets inventory. If complete, prepare writing; else design queued experiments, Lean or proofs.
| 6 | 01:51 | 01:52:00 (taken 01:50; +1 min, on time) | Alarm 7 armed (bfasrm7wj → 02:51). Disk 24 GB; swap 10.1 / 11.3 GB; load 18 (4 sims + 1 viewer + watcher). Since wake 5: C-104 N4 REJECTED; C-105 GQ no; C-106 HYB / HYBQ; C-107 X3 INFO-LIMITED; C-108 TSI registered; C-109 N3; C-110 / C-111 TSI SELECT (2, 0), one-shot; C-112 two job failures fixed; C-113 the user's review corrections; **C-114 TSI CONFIRMATION FAIL (agent TL +0.85; fuel −4.56 %, city −0.20, human −1.23), KT-1 PASS**; C-115 TSI-2 registered. Queue: 036 N8 running → 036z TSI-2 → 037 variants → 038 SHIFT. Dashboard generic (registry only), watcher in the background. User: writing only from 05:00, after the 04:52 research. |
| 7 | 02:51 | 02:51 fired; **NOT re-armed** | Results read at 02:36–02:48 (C-118 TSI-2 PASS → **M3 MET**; C-119 variants closed; SHIFT finished 02:48). **My failure:** I did not re-arm after alarm 7, and my session then hit the usage limit. Wake 8 (03:51) was MISSED; GEN finished at 03:11, unread until 04:52. |
| 9 | 04:51 | taken 04:52 (manual) | Alarm armed → 05:51. Disk 20 GB. C-120 SHIFT holds; C-121 GEN (R8 / R9 / ρ / c2 ablation / H-PATH). Queue EMPTY. Now: the 04:52 research duty; writing from 05:00. |
| 10 | 05:51 | 05:52 | Alarm armed → 06:51. Queue empty. Since wake 9: C-122 PERF (the adapter halves the publication sensitivity); manuscript rewritten from 05:00 (abstract, intro, M3 = TSI, related work, limitations); 94 / 94 numbers present in the reports. Next: semantic read-through, the Setting section, references. |
| 11 | 06:51 | 06:52 | Alarm armed → 07:51. Queue empty; no user message since 05:5x (the spider port is offered, not started). Draft compiled; three references verified. |
| 12 | 07:51 | 07:52 | Alarm armed → 08:51. Since wake 11: user "còn gì cần chạy? research chưa?" → spider TSI built and run (C-123 attempt 1 FAIL; C-124 attempt 2 FAIL; the mechanism replicates); manuscript updated (abstract, M4, limitations); dashboard updated (4 entries; frontier outliers listed). Queue empty. |
| 13 | 08:51 | 08:52 | Alarm armed → 09:51. User sent PAPER_FREEZE_ASSESSMENT → experiments closed; manuscript corrected; claim map locked (C-125). Queue empty. Remaining text work: layout overfulls, unverified references, the 11:51 summary. |

## Wake 09:51 — MISSED

- The alarm (b9ii0lwn3) was killed when the previous session ended, and the session limit lasted until 09:50.
- Resumed 09:58: alarm re-armed for 10:51 (b9c5y929p); disk 18 GB free; swap 9.8 / 11.3 GB; queue empty.
- Work: full manuscript review (C-127).
