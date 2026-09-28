#!/usr/bin/env bash
# Frozen-actor screening: global broadcast tables -> offline neural selectors.
# Deliberately not a learned-MARL/end-to-end latency benchmark.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:-research/marl_budget/cheap_pilot_$(date +%Y%m%d_%H%M%S)}"
if [ -e "$RUN" ]; then
  printf 'Refusing to overwrite existing run: %s\n' "$RUN" >&2
  exit 2
fi
mkdir -p "$RUN"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1
export PYTHONDONTWRITEBYTECODE=1
PY="external_envs/runtime/bin/python"
"$PY" -u scripts/MARL_cheap_screen.py --profile pilot --out "$RUN/data" 2>&1 | tee "$RUN/collection.log"
"$PY" -u scripts/MARL_cheap_pilot.py --data "$RUN/data" --out "$RUN/models" --epochs 150 --seeds 0 1 2 2>&1 | tee "$RUN/training.log"
printf '\nResults: %s/models/report.json\nRaw subset/action/return tables: %s/data/tables.jsonl.gz\n' "$RUN" "$RUN"
