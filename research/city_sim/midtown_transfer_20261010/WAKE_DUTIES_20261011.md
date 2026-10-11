# Wake duties, night of 11/10/2026 (user 02:4x: "coi chỗ nào còn fail hay lỗi thì cải tiến đi, ... bug thì sửa đi, đặt báo thức mỗi tiếng dậy để làm việc; phiên đầu tiên bắt đầu là 2 tiếng 17 phút nữa")

Alarms are background `sleep` commands (cron is unreliable here). The first is at 05:02, then every hour. At each wake, set the next alarm FIRST, then work.

## At every wake, in order
1. Run `date`. Check:
   - `research/queue_mt_20261011/spool.out`, `running/`, `failed/`;
   - `df -h /`, `sysctl vm.swapusage`, `uptime`.
   - The disk guard is 15 GB. If the load is extreme, stop only my own preview animation; kill nothing else.
2. **A failed job:**
   - read `logs/<job>.log`, diagnose and fix the cause;
   - re-queue as a NEW job file with a new number. Never edit a running script; never delete outputs (`legacy/`).
3. **A finished job:**
   - run `scripts/MT_report.py`;
   - check that its outputs are COMPLETE and that training under `MT_TTT=-1` had ≈ 0 teleports;
   - write the result into the protocol (Results section) and a ledger row (`research/city_sim/CITY_LEDGER_20261002.md`), with `date` output as the time stamp.
4. **The Midtown fleets** (`retrain/fleets/MT<seed>_fleet.pt`, expected ≈ 04:10): check all four exist before job 306 starts. Otherwise hold 306 and investigate.
5. **When a light arm is complete:** add it to the demo page as a "trained on Manhattan" comparison:
   - honestly labelled, whatever the result;
   - the clip is test day 3, model t59, `DEMO_record.py`;
   - rebuild with `scripts/DEMO_build_page.py` and verify in the browser (then leave the pane on a static page; the animated page costs about 140 % CPU).
6. Work the improvement backlog below, then report briefly (Vietnamese).

## Improvement backlog (status kept here)
- [x] Demo page under 16 MB: 11.2 MB with Midtown clips at 2 s per frame (`dt`). Verified in the browser at 02:4x.
- [x] Forecast refit for Midtown lights: `scripts/RUN_mt_forecast.sh` (MT-A6), smoke + KMT6 PASS. Queued as jobs 308 (grid / A4 / ft lights) and 309 (tests MTR_BGF, MTR_BMM_a4, MTR_BMM_ft). Open: forecasters for the gated / per-light arms need a widen() port.
- [x] Residual teleports with teleports off: 0–4 per seed over 120 episodes in every arm (wake 1). Negligible; probably collisions or disconnected routes. Not classified further.
- [~] Realistic Midtown demand from the downloaded NYC data (`research/city_sim/data/nyc_open_20261011/`). Step 1 done at wake 2 (edge→zone map, hourly taxi OD). Plan MT-B registered in the protocol. Next: match DOT counts to edges, build the demand generator, calibrate on half the segments:
  - taxi OD by zone and hour;
  - DOT counts on 113 segments for calibration and validation.
  - Larger task: needs a protocol first.
- [ ] Football: ACI for futures B/C (the football session's scope; only if the user asks).

## Wake log
- 05:02 wake 1: 303–305 done (gated / local arms fail: overfit), 306 running. Demo + protocol + ledger C-236 updated. Next alarm 06:02.
- 06:02 wake 2: no failures. Found: the Midtown net covers only W 29–58 / E 34–61 St (74 km, 702 OSM ways); demo text corrected (was 23rd–66th), protocol correction added. DOT counts: 24/60 targets match an edge in direction (others on roads absent from the net). A fuller OSM extract would need a download (ask the user). Job 308 at the N2-fit stage of set 1 (slow: ~38 % CPU per fit, swap 9.2 GB). MT-B step 1 done. Next alarm 07:02.
- 06:2x (user awake): full Overpass fetch running in the background with retries (servers overloaded at 06:20); when it finishes (task notification) launch `scripts/RUN_mt_full.sh` in the background IMMEDIATELY (user: 'tải xong thì chạy lại thí nghiệm trên map đầy đủ luôn'), in parallel with the queue; if the fetch failed after 8 attempts, retry at the next wake.
resume with: kill -CONT 63827 63838 63910 64344 64690
- 06:4x: overload (load 102). Job 308's five N2 fits PAUSED (SIGSTOP) so MT-C (full map) runs first. ORDER when MT-C finishes: (1) launch scripts/RUN_mt_full_cap.sh (MT-D, max green 50 s); (2) when MT-D finishes, resume 308 with `kill -CONT 63827 63838 63910 64344 64690`. Never run MT-D and the 308 fits at the same time. The user stopped the hourly alarm (07:02): do not re-arm unless asked.
- 06:52: MT-D cap does not help (not run). MT-E (AI + actuated rest) diagnostic: 126 s vs ACT 163 s, 20 teleports. NEW ORDER when MT-C finishes: (1) launch scripts/RUN_mt_full_actrest.sh (MT-E, 6 lanes); (2) after MT-E, resume 308 with `kill -CONT 63827 63838 63910 64344 64690`.
