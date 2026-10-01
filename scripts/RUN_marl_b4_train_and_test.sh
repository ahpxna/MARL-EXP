#!/usr/bin/env bash
# B4 (PROTOCOL_B4_DAGGER_20260927.md §2-§3): retrain on prefix + on-policy data, development
# closed loop on 501-508, then the preregistered closed-loop test on fresh seeds 801-816.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:?b4 run dir}"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY="external_envs/runtime/bin/python"
"$PY" -u scripts/MARL_hetero_top2_joint_dev.py --run "$RUN" --out "$RUN/top2_joint" --threads 4 > "$RUN/train_top2_joint.log" 2>&1
echo "top2_joint retrained $(date)"
"$PY" -u scripts/MARL_hetero_mitigation_dev.py --run "$RUN" --out "$RUN/controls" --learners ctrl_history ctrl_public bid_queue --threads 4 > "$RUN/train_controls.log" 2>&1
echo "controls retrained $(date)"
cat > "$RUN/dev_map.json" <<JSON
{"ctrl_history": "$RUN/controls", "ctrl_public": "$RUN/controls", "bid_queue": "$RUN/controls", "mlp_top2_joint": "$RUN/top2_joint"}
JSON
"$PY" -u scripts/MARL_hetero_closed_loop_v2.py --dev-map "$RUN/dev_map.json" --out "$RUN/cl_dev" --learners ctrl_history mlp_top2_joint --traffic-seeds 501 502 503 504 505 506 507 508 --cap 84 --policy direct > "$RUN/cl_dev.log" 2>&1
python3 scripts/MARL_hetero_b3_verdict.py "$RUN/cl_dev" > "$RUN/cl_dev_verdict.txt"
echo "development closed loop done $(date)"
"$PY" -u scripts/MARL_hetero_closed_loop_v2.py --dev-map "$RUN/dev_map.json" --out "$RUN/cl_test" --learners ctrl_history mlp_top2_joint --traffic-seeds $(seq 801 816) --cap 84 --policy direct --oracle > "$RUN/cl_test.log" 2>&1
"$PY" -u scripts/MARL_hetero_closed_loop_v2.py --dev-map research/marl_budget/b2_freeze_20260927/dev_map.json --out "$RUN/cl_test_frozenB2" --learners mlp_top2_joint --traffic-seeds $(seq 801 816) --cap 84 --policy direct > "$RUN/cl_test_frozenB2.log" 2>&1
python3 scripts/MARL_hetero_b3_verdict.py "$RUN/cl_test" > "$RUN/cl_test_verdict.txt"
echo "closed-loop test done $(date)"
cat "$RUN/cl_test_verdict.txt"
