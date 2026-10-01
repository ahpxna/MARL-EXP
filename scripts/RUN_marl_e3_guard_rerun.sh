#!/usr/bin/env bash
# PROTOCOL_E3_CLOSED_LOOP_GUARD_20260928.md (ledger L-65): rerun existing E3 closed-loop panels with the SAME frozen
# checkpoints and the SAME arguments (read from each original manifest), under closed loop v6 --guard support.
# Output <actor>/<panel>_v6g next to the original <actor>/<panel> (kept unchanged).  Skipped when complete; refuses a
# directory with a live writer.  Usage: bash scripts/RUN_marl_e3_guard_rerun.sh <panel name> <actor dir>...
#   panel name: cl_v3_direct (v2 ablation selectors) or cl_direct (v1 selectors)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
PANEL="${1:?panel}"; shift; PIDS=""
for A in "$@"; do
  SRC="$A/$PANEL"; OUT="$A/${PANEL}_v6g"
  [ -f "$SRC/manifest.json" ] || { echo "skip $A: no $PANEL"; continue; }
  [ -f "$OUT/manifest.json" ] && { echo "done $OUT"; continue; }
  bash scripts/e3_writers_check.sh "$OUT" > /dev/null || { echo "refusing: live writer on $OUT"; exit 3; }
  [ -e "$OUT" ] && mv "$OUT" "legacy/$(echo "$OUT" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  ARGS=$(python3 - "$SRC/manifest.json" <<'EOF'
import json, sys, shlex
a = json.load(open(sys.argv[1]))['args']
sel = a['selectors'] if isinstance(a['selectors'], list) else [a['selectors']]
out = ['--actor', a['actor'], '--selectors', *sel, '--names', *a['names'], '--policy', a['policy'], '--cap', str(a['cap']),
       '--capacity', a.get('capacity', 'iid'), '--headways', *[str(h) for h in a.get('headways', [8.0, 16.0])],
       '--traffic-seeds', *[str(s) for s in a['traffic_seeds']]]
if a.get('mp2'):
    out.append('--mp2')
print(' '.join(shlex.quote(x) for x in out))
EOF
)
  echo "launch $OUT: $ARGS --guard support --t-min 7 --z-max 50 $(date)"
  eval "$PY -u scripts/MARL_e3_closed_loop_v6.py $ARGS --guard support --t-min 7 --z-max 50 --out '$OUT'" > "$OUT.log" 2>&1 & PIDS="$PIDS $!"
done
rc=0; for p in $PIDS; do wait $p || rc=$?; done
echo "guard rerun $PANEL done rc=$rc $(date)"; exit $rc
