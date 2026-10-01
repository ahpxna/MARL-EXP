# Reproducing the MARL results and figures (28/09/2026)

Run every command from the repository root with the managed runtime:

```
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
```

Artifacts carry their producer hashes in `manifest.json`. The `*.pt` checkpoints and the CityFlow
scenario inputs are outside git; their sha256 values are in `UNCOMMITTED_ARTIFACTS_MANIFEST_20260928.json`,
and the scenarios regenerate deterministically from (seed, headway).

## Two-minute smoke of the whole E3 chain

- `SMOKE=1 bash scripts/RUN_marl_e3_long.sh <new dir> 0` covers actor, message use, labels,
  selectors, closed loop, report and fig3.
- `SMOKE=1 bash scripts/RUN_marl_e3_ablation.sh <that dir>/actor_s0` covers the four-variant
  ablation.

## Fixed-MP2 results

| result | command | artifact |
|---|---|---|
| B2 held phase (preregistered) | `bash scripts/RUN_marl_b2_confirm_v2.sh` | `b2_confirm_20260927_225002/` |
| B3 / B4 closed loop | `bash scripts/RUN_marl_b4_train_and_test.sh <dir>` | `b4_run_20260927_230436/cl_test/` |
| comparison panel | `$PY scripts/MARL_hetero_closed_loop_v3.py …` (manifest args) + `MARL_hetero_closed_loop_v4.py` (request baseline) | `cl_baselines_20260927_232931/`, `cl_w2c_bin_20260927_234219/` |
| target diagnostic | `$PY scripts/MARL_hetero_target_diag.py --out <dir>` | `target_diag_20260928_000455/` |

## Figures

| figure | command |
|---|---|
| F1 scene | `$PY scripts/MARL_make_fig1_scene.py` |
| F3 closed loop (fixed MP2) | `$PY scripts/MARL_make_fig3_v4.py --run … --extra … --drop where2comm_top2` (arguments in the figure JSON) |
| F4 mechanism | `$PY scripts/MARL_make_fig4_mechanism.py` |
| E3 fig3 / frontier | written by `RUN_marl_e3_long.sh`, `RUN_marl_e3_ablation.sh`, `RUN_marl_e3_frontier.sh` into `<actor dir>/figures/` |

## E3 (learned actor)

- Protocols: `PROTOCOL_E3_PILOT_20260928.md`, `PROTOCOL_E3_SCRATCH_20260928.md` and
  `PROTOCOL_E3_ABLATION_20260928.md`.
- Chains: `RUN_marl_e3_long.sh` (BC + MAPPO) and `RUN_marl_e3_long_scratch.sh`.
- After a CityFlow hang: `RUN_marl_e3_resume.sh`, `RUN_marl_e3_schednet_resume.sh` and
  `RUN_marl_e3_after_hang.sh`. Each uses `scripts/run_with_watchdog.py`.

## Lean

```
cd work/p13_conjectures && RUN=<name> J=2 bash verify_all.sh
```

This is a full gate over MODS; the last one is `full9_20260928`, VERIFY PASS.
