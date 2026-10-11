# One-hour wake duties (standing instruction from the user, 03/10/2026 00:4x–01:0x EDT)

User (verbatim, abridged): "đặt báo thức mỗi 2 tiếng dậy để trả lời cho câu hỏi giờ những việc cần làm để tới đích là gì? mà
đích là gì đã? research và xem coi đích t cần đến là gì? cần 1 câu chuyện thật hay và thật novelty, đủ hấp dẫn, tính thiết thực
cao, ... mọi yếu tố cần có thêm để publish.  Và coi lại toàn bộ results và check và báo cáo tiến độ các tiến trình hiện tại, sau đó
bắt đầu research đọc cả method và discussion của các bài đó chứ không phải mỗi abstract hay introduction, xem các phương pháp
hiện tại đã ok chưa? đã giống người chưa? nhưng đã đủ mới ở những chỗ cần novelty chưa? các kết quả của người ta nói lên điều
gì? khác gì mình? tại sao? report lại tất cả ... và tiếp tục xem các results của bản thân, tất cả asset, chọn lọc và lần lượt
kiểm chứng các giả thiết sau khi research, thiết kế thêm thí nghiệm bỏ vào hàng chờ, check hàng chờ ... đó là sơ bộ nhiệm vụ
bắt buộc mỗi lần 2-hours wake up; khi nào cần t sẽ thêm task vào."  Changed by the user (00:5x–01:0x): ONE-hour wakes, the
first one kept at 02:40; up to 2 subagents per wake.

**Hypotheses source (task T-1) — full path:**
`/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/DECISION_FORKS_AND_HYPOTHESES_20261003.md`
(G1–G8 with falsifiers, §4; worker steps, §8).  Companion files in the same folder:
`/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/ri_age_role_bayes_check_20261003.py` (+ `.json`, the G1 Bayes
calculation; reproduced 00:37 from a scratchpad copy) and
`/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/PROJECT_EVIDENCE_CATCHUP_20261003.md`.  These are outside the repo:
read them, never edit them.

## Wake mechanism (and its limits)
* One background timed alarm at a time: Bash run_in_background `caffeinate -i -t <seconds to the next target>; date
  '+WAKE-ALARM-n fired …'`.  Its completion notification re-invokes the session; caffeinate also keeps the Mac from
  idle-sleeping meanwhile.
* **At every wake, the FIRST action is to re-arm the next alarm** (before any work), then `date`, then a line in the wake log
  below.  Exactly one alarm pending at any time (check with `ps -axo pid,etime,command | grep "caffeinate -i -t"`).
* Not CronCreate (fired 1 of ~20 times on 02/10 — memory feedback_cron_checkins_unreliable).
* Known limit: the alarm lives in this Claude session; if the app or session is closed, the chain stops (the experiments, which
  run under nohup in the terminal, do not).  The first two firings are verified and reported to the user.

## Mandatory duties at every wake (in order)
* **W0 Re-arm + log.**  Re-arm the alarm; `date`; append to the wake log.
* **W1 Destination ("đích").**  Keep DESTINATION_20261003.md current: the target story (one sentence + the three claims), the
  venue(s) and their bar, and the full publish checklist (novelty vs the closest work, practical motivation, standard benchmarks
  and published baselines, seeds / statistics, theory and Lean status, ablations, failure cases, reproducibility, limitations:
  no real controller logs, no J2735 traces, no independent vehicle stack, no real city cross-version data).  Answer: what remains
  between now and the destination, in order.
* **W2 Progress.**  Every running process and queue: progress, stalls / FAIL / retries, ETA (measured rates, `date`); every
  finished report read against its registered predictions (AGENTS.md audit rules: trace claim → code → raw → statistic).
* **W3 Literature, read deeply.**  For the nearest papers: METHOD, EXPERIMENTS and DISCUSSION (not abstract / introduction
  only).  For each: what they do, what their results say, how it differs from ours, why; whether our methods are sound and
  standard (like theirs) where they should be, and new where novelty is claimed.  Notes in LITERATURE_DEEP_READ_20261003.md.
* **W4 Own results and assets.**  Re-read our results and assets (E3, city, RI, Lean, old A/B/C assets); select the hypotheses
  the research bears on and verify them one by one (cheapest first: existing data, analytic computations).
* **W5 Experiments + queue.**  For the hypotheses that need runs: novelty check → protocol (predictions before results) →
  smoke → queue.  Check the queue: capacity (load, disk ≥ 15 GB), priorities, stalls, what to add or retire.
* **W6 Report.**  A short Vietnamese report to the user (progress, answers to W1/W3, what was verified, what was queued);
  ledger rows and dashboard registry updated.

## Standing constraints that apply to every wake
No subagents / Workflow unless the user's own message says "fetch" (then reuse the roster agents).  No killing processes
without the user's instruction.  Never edit a running script.  Protocol before runs; smoke first; `python -u`; nohup in the
user's terminal for long runs; ≤ 6 Claude terminal tabs.  Downloads need explicit permission.  Never delete; archive to legacy/.
No commit unless asked.  Reports in Vietnamese.  Do not edit ROADMAP / OPEN_MATH / THEOREM_MAP.  Nothing enters a manuscript as
a theorem before the Lean gate.  CoLight NYC data: never redistribute.

## Tasks added by the user
* **T-1 (00:5x 03/10): verify the reviewer's G1–G8 one by one, after the research (W3), cheapest first; design experiments
  for the ones that need runs and queue them.**  Source: the user's paste (external review 3) and its memo
  /Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/DECISION_FORKS_AND_HYPOTHESES_20261003.md (falsifiers there).  G1–G8
  are the reviewer's proposals, not pre-registered and not renaming our H / B items.
  | G | Hypothesis | Next check (reviewer) | Status |
  |---|---|---|---|
  | G1 | upgrade hazard = receiver EXCESS risk while information improves | Bayes line in RI; same split on C0's Bayes tables | SUPPORTED (wake 1, agent B, spot-verified): excess < 0 in 20/20 seed pairs both directions; information term ≥ 0 (paired 3×3 +0.83 / +0.72 — corrects Add. 1's unpaired −0.13); C0 exact split: excess rises on 8/9 lights. Caveat: matched-receiver proxy vs exact floor Spearman 0.33 (NOVELTY_POSITION Add. 2) |
  | G2 | an input repair works iff it keeps the payload–age–target relation | remap vs emulation vs current-state estimator vs adapter | DONE (L-295): EM2 SUPPORTED on 4×4 (EMU − LAB +4.63, 9/10; rank version also + on both nets) — coupling matters; EM1 / EM3 NOT (no repair vs PLAIN; harmful at K2 / K3) — the hazard is joint-configuration; repairs must act on the joint level (training, FB_S) |
  | G3 | out-of-support mass matters only weighted by decision disadvantage | C0 tables: OOS mass vs action-disadvantage-weighted OOS | wake 1 (agent B): ranking NOT better (0.873 vs 0.867; held-out 0.880 vs 0.831, reverse equal) → reviewer's kill rule fires for a transferable scalar; magnitude RMSE −40 %; C0 cannot decide further (nested OOS lights); needs lights with equal OOS mass but different disadvantage |
  | G4 | the contract must predict the exposure the PAIR generates (closed loop) | human-log vs receiver stub vs real fleet, same ckpt / seed | Q7b done 01:01: B3 NOT SUPPORTED (contract 0.36 vs free 0.40); with-fleet K_contract tracks OOS (0.94) but OOS ranks harm only 0.52 → G4 test needs a behaviour stub; design next |
  | G5 | a receiver-specific threshold keeps more gain than a common one | cap frontier with receivers of different boundary | Q7b: B2 held (cap 50 keeps 89 % of gain, harm 37 %), B5 NOT SUPPORTED (no knee at τ_max) → day wake 1: B drafted the G5 protocol; Gate 0 (human traffic: greens ≤ 19 s on every max-green net) and Gate 0b (fleet present: τ reaches M, but τ > 50 on ACT80 only 0.84 %) → feasible, low-power (C-10). Earlier: all four L-ACT fleets have τ_max = 50 s (set by ACT's max green, not by the seed), so Q7b CANNOT test G5; needs fleets trained against ACT lights with max green 40 / 60 / 80 (design next wake).  Side reading: at cap 50 the fleet is in support (K ≈ 0.003) yet r = +4.05 — in-support harm, as B4 / G3 |
  | G6 | finding ONE acceptable upgrade by paid tests is cheaper than validating the library | small library, paid rollouts, valid stopping, vs uniform / adaptive | later; prior art: feasible BAI 2511.09808, policy testing (PMLR 300) |
  | G7 | the reconstruction floor can exceed the task floor; frozen-receiver floor is a third object | separate the three floors (Lean scope) | wake 2 (agent A, verified names + gate list): G7_FLOORS_SCOPE_20261003.md — R (dynamic, Lean) / T (static only) / F (instance only, not monotone); candidate Lean L1–L3; paper wording 'knowledge floors', 'compiled, smoke-gated'; 3 modules missing from verify_all.sh |
  | G8 | two compatible endpoints do not make a partial rollout compatible | cohort upgrades + temporary compatible mode | later |

## Schedule (user 00:5x 03/10; changed to hourly 00:5x)
Wakes **every hour**: 02:40 (first, as the user set), 03:40, 04:40, 05:40, 06:40, 07:40, 08:40 EDT on 03/10, then stop (the
user: "cho đến 9h").  At each wake the re-armed alarm targets the NEXT clock time exactly (seconds = target − now, computed
with `date`), so the time spent working does not drift the schedule.  At the 08:40 wake: do NOT re-arm; tell the user the
cycle has ended.

## Schedule extension (user 10:1x 03/10: "tiếp tục đặt báo thức 1 tiếng cho tới 7 giờ tối")
Hourly wakes resume at **10:40, 11:40, 12:40, 13:40, 14:40, 15:40, 16:40, 17:40, 18:40** EDT on 03/10 (last before 19:00); each
alarm armed ≈ 55 s early (target hh:39:05) because caffeinate fired ≈ 1 min late overnight.  Same duties W0–W6, T-1, ≤ 2
subagents per wake.  At the 18:40 wake: do not re-arm; tell the user the cycle has ended.

## Subagents on wakes (user 00:5x 03/10: "mỗi lần dậy m có thể fetch 2 thằng subagents ra giúp m")
At each wake I MAY fetch up to 2 subagents.  Reuse the roster agents (research/papers/audits/AGENTS_ROSTER_20261001.md) with
SendMessage so they keep their context: (A) a5e043f5fc399c33b — Lean / papers / old-directions miner → W3 deep reading and
G7 / old assets; (B) acae5606e7dd259e7 — experimental-artifact miner → W2 / W4 checks (G1, G3 computations on existing
data).  Only if one cannot be resumed: re-create it with the same role and brief, say so, and update the roster.  Briefs are
read-only (no runs, no edits to producers / protocols / ledgers), must not open pending pre-registered target outputs, and
their reports are verified by me before anything is recorded.  Never more than 2 per wake.

## Wake log
| # | armed | fired | notes |
|---|---|---|---|
| 1 | 00:55:19 EDT 03/10 (6300 s; the 00:52:02 7200-s alarm was stopped — user 00:5x: first wake in 1 h 45 min) | **fired 02:41:18** (≈ 1 min late; verified) | after this one, alarms target the next hour mark (03:40, 04:40, … 08:40); user 00:5x: do NOT start a cycle now, status only. W1 note found meanwhile: AAMAS 2027 abstract deadline 1 Oct 2026 has passed (paper 8 Oct); AAAI fast track 11 Dec 2026 |
| 2 | 02:41:3x EDT (to 03:40:00) | **fired 03:41:00** (≈ 1 min late; verified) | wake 1 did: Q7b read + C-8; DESTINATION v1; deep read (A) + CALF correction; G1/G3 (B) + Add. 2 + C0 sha bug fixed (C-9); G5 not testable in Q7b; emulation protocol + Amendment 1 + queue |
| 3 | 03:41:1x EDT (to 04:40:00) | **fired 04:41:01** (verified) | wake 2 did: disk dip found (03:12 every launcher refused) → relaunched sequential chain 03:45 + D lane 3; L-291 + memory; agents A (G7 + compat/drift lit) and B (train×deploy matrix) resumed and reported (verified: matrix = stored reports, gate list, theorem names); G7_FLOORS_SCOPE, LITERATURE wake-2 (BCT update gain = our split), e3_train_deploy_matrix_20261003 saved; PAPER1_OUTLINE v1; cross-channel flip probe written + smoked + protocol + launched 04:01 (tab c23) |
| 4 | 04:41:2x EDT (to 05:39:05, ≈ 1 min early to land at 05:40) | **fired 05:40:06** but NOT processed: the account hit its usage limit (≈ 05:0x–07:40); the 06:40 alarm was therefore never armed — wakes 05:40 and 06:40 MISSED | wake 3 did: alarm 3 fired 04:41:01; flip probe FL1–FL4 SUPPORTED (L-292); agents A (standard comm-MARL benchmark survey) and B (paper-1 figures) resumed; G5 design started |
| 5 | 07:41:4x EDT (to 08:39:05; last) | **fired 08:40:04** (verified) | wake at 07:41 after the usage-limit reset: FB, test D, emulation, flip results read + ledger L-293…L-295; NYC resumed 06:39 (it ≈ 299); agents A / B resumed (they had been stopped by the same limit) and reported: A — benchmark survey + RDC anticipation (verified verbatim; NOVELTY Add. 3); B — draft figures F1–F5 (reviewed, copied to research/papers/_figures/paper1_draft_20261003/, sent to the user) |
| — | not re-armed (schedule ends at 08:40, user: until 9h) | — | final wake 08:40: NYC teachers ≈ 500/2000 (≈ 200 it/h → teachers ≈ 16:00, then students + evals); free 21 GB, swap 3.7 / 5 GB; no REFUSED/FAIL; CYCLE ENDED, user told |
| D1 | 10:18:4x EDT (to 10:39:05) | **fired 10:40:05** (verified, on time) | day schedule started (user 10:1x); wake: JT 3×3 17/35 after 7 min, NYC teachers ≈ 765/2000, free 22 GB, swap 3.5 / 5 GB, no REFUSED/FAIL; next alarm ≈ 11:40 |
| D0 | (user 10:2x: 'làm đợt 1 từ bây giờ') | — | round 1 now: commit 4e8fe126 pushed (4 325 files, 158 MB; CoLight data, scenario copies, tripinfo excluded; .gitignore extended); joint-throttle experiment written, self-checks (k = ∞ shadow merge = active merge on 3×3 and 4×4 after a fix caught by the self-check), protocol + smoke + queue launched 10:33 (tab c24); agents A (Lean L2 draft) and B (G5 city design) resumed |
| D2/D3 | (armed 10:40) | **fired 11:40:05** but NOT processed — usage limit ≈ 10:50–12:40; the 12:40 alarm was never armed; wake processed at 12:41 instead | — |
| D4 | 12:41:4x EDT (to 13:39:05) | (due ≈ 13:40) | wake 12:41 (after the 2nd usage limit): JT final read (L-296: JT3 SUPPORTED — masked reference far below Z; receiver-side throttle NOT a repair on 4×4: co-production by the sender-side mirror); dedupe started (free 17 GB); Mahalanobis-gate baseline written (v2 + FB_Mq), protocol, parity check on 1 panel episode (FB_S only), queue launched (tab c25); agents A (Lean L2, resumed) and B (paper-1 Related work + Results draft) |
| D5 | 13:40:2x EDT (to 14:39:05) | (due ≈ 14:40) | wake 13:40 (alarm fired 13:40:05, on time): FBM 50/120, NYC ≈ 1460/2000, free 25 GB; since 12:41: Lean L1/L2 verified + moved + gate list (L-299), matrix ledger row (L-298), draft Related/Results copied, dedupe −11 GB (L-297); agents A (verify [VERIFY] literature from PDFs) and B (audit protocols vs report code) resumed |
| D6 | 14:40:2x EDT (to 15:39:05) | (due ≈ 15:40) | wake 14:40 (alarm 14:40:05, on time): FBM 94/120, auto-dedupe 14:17 freed 4.70 GB (free 27 GB), NYC ≈ 1685/2000; since 13:40: [VERIFY] items resolved + RDC correction (Add. 4), audit L-300 (Spearman ties fixed pre-result, FB6 reprinted, EM4 by construction); agents B (PCT / dissonance receiver fine-tune design) and A (paper-1 theory section draft) resumed |
| END | — | — | the 15:40 alarm fired but was NOT processed (usage limit ≈ 15:0x–17:40); 16:40 / 17:40 never armed. **Cycle STOPPED by the user at 17:4x** ('dừng loop 1 tiếng đi'); no alarm pending (checked). Agents asked for handover reports. |
