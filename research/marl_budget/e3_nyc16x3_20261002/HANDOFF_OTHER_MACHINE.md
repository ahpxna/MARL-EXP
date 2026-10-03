# Running the NYC 16×3 chain (PROTOCOL_E3_NYC16X3_20261002) on another machine (written 03/10/2026 00:1x EDT)

## Why move it
On this Mac (10 cores, 16 GB) with test D, the fallback queue and Q7b also running, a NYC teacher iteration takes ≈ 85 s (load
27–150): 2 000 iterations ≈ 2 days before the students even start.  The chain is CPU-only (CityFlow + small torch nets).

## Recommended: start FRESH there (do not move the half-trained teachers)
The local teachers are at iteration ≈ 50 / 2 000 (≈ 1 h of work).  Resuming them elsewhere would mix two machines inside one
training run (floating-point and thread differences); a fresh start keeps provenance clean.  After the remote run is
confirmed, stop the local NYC lanes (only on the user's instruction) and archive research/marl_budget/e3_nyc16x3_20261002/actors
to legacy/.

## Files
* The repository (scripts/, models/, envs/, external/, research/marl_budget/PROTOCOL_E3_NYC16X3_20261002.md,
  research/marl_budget/PROTOCOL_E3_SUPPORT_FALLBACK_20261002.md, research/marl_budget/e3_payload_codebook_20260929.json).
  UNCOMMITTED and needed (commit when the user asks, or copy): scripts/MARL_nyc_scenario.py, MARL_nyc_wrapper.py,
  RUN_marl_nyc.sh, RUN_marl_nyc_teacher.sh, QUEUE_marl_nyc_20261002.sh, MARL_e3_fallback_eval.py, MARL_e3_fallback_report.py,
  RUN_marl_e3_fallback.sh, MARL_e3_nyc_report.py.
* Data (NOT in git: CoLight data carry no licence — copy privately, never publish): research/city_sim/data/nyc_colight_16x3/
  (roadnet_16_3.json sha256 918fe133…, anon_16_3_newyork_real.json f8cbaaae…; the scenario module asserts both).

## Runtime (must match these pins)
* Python 3.12 venv at external_envs/runtime: numpy==1.26.4, torch==2.10.0, scipy==1.17.0, msgpack-numpy==0.4.8.
* CityFlow from https://github.com/cityflow-project/CityFlow at commit 81ee0f47659ca66177a71f81676691c58ee89184, cloned to
  external_envs/repos/CityFlow and installed with `pip install -e` (needs cmake and a C++ compiler).
* Create the marker file external_envs/runtime/.cig-external-runtime-ready (envs/external/runtime.py checks it); the run scripts
  export CIG_EXTERNAL_RUNTIME_ACTIVE=1 themselves.
* Smoke there first: `SMOKE=1 bash scripts/RUN_marl_nyc.sh 0` (≈ 20–40 min; writes under e3_nyc16x3_20261002/smoke_chain and
  e3_fallback_20261002/smoke_nyc_chain), then both reports with --smoke as on this machine.

## Run
`nohup bash scripts/QUEUE_marl_nyc_20261002.sh > research/marl_budget/e3_nyc16x3_20261002/queue.log 2>&1 &`
Peak per seed ≈ 7 cores (3 students × --threads 2 + evaluations); 5 seeds ≈ 35 cores for full parallelism (runs on fewer, slower).
Disk: keep ≥ 15 GB free (the launchers refuse below that); v9 students keep a resumable state file of up to ~1 GB each.
Record the machine (`uname -a`, CPU model, core count) in a note beside queue.log.

## Bring back
research/marl_budget/e3_nyc16x3_20261002/ (actors, eval, ruleA_s*.json, report.txt) and research/marl_budget/
e3_fallback_20261002/nyc/ (+ report_nyc.txt, verdict_nyc.json) — rsync back, then the ledger row and the dashboard.
Panel 5001–5064 must not be used by anything else on either machine.
