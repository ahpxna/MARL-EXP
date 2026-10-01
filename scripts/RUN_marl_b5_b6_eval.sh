#!/usr/bin/env bash
set -euo pipefail
cd "/Users/phanan/cig-amf-main"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python
pids=()
$PY -u scripts/MARL_hetero_b2_confirm_v2.py --dev-map research/marl_budget/b5_freeze_20260927/dev_map.json --confirm-run research/marl_budget/b5_panel_20260927_231835 --freeze research/marl_budget/b5_freeze_20260927/freeze.json --out research/marl_budget/b5_panel_20260927_231835/confirm > research/marl_budget/b5_panel_20260927_231835/confirm.log 2>&1 &
pids+=($!)
for p in cap_fixed cap_bursty cap_low cap_high; do
  $PY -u scripts/MARL_hetero_panel_eval.py --run research/marl_budget/b6_panels_20260927_231905/$p --dev-map research/marl_budget/b6_dev_map.json --out research/marl_budget/b6_panels_20260927_231905/$p/eval_liveK.json --live-only > research/marl_budget/b6_panels_20260927_231905/$p/eval.log 2>&1 &
  pids+=($!)
done
for p in load_12 load_24 load_5; do
  $PY -u scripts/MARL_hetero_panel_eval.py --run research/marl_budget/b6_panels_20260927_231905/$p --dev-map research/marl_budget/b6_dev_map.json --out research/marl_budget/b6_panels_20260927_231905/$p/eval_all.json > research/marl_budget/b6_panels_20260927_231905/$p/eval.log 2>&1 &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "B5/B6 evaluation done $(date)"
