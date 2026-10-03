#!/usr/bin/env bash
# City main queue (02/10/2026 19:1x; PLAN_CITY_IDEAS_20261002.md): Q1 C0 v3 seeds after its panels, merge; then Q4 corridor.
cd /Users/phanan/cig-amf-main; PY=external_envs/runtime/bin/python; D=research/city_sim/c0_v3_20261002; Q=research/city_sim/q4_corridor_20261002
echo "wait C0 panels (23416 23418 23420 ) $(date)"; for p in 23416 23418 23420 ; do caffeinate -i -w $p 2>/dev/null; done
ls $D/panels/*_eval.npz | wc -l
echo "C0 seeds start $(date)"; pids=()
for s in 0 1 2; do nice -n 12 $PY -u scripts/CITY_c0_testbed.py --out $D --seed $s --extra > $D/seed_$s.log 2>&1 & pids+=($!); done
for s in 3 4; do nice -n 12 $PY -u scripts/CITY_c0_testbed.py --out $D --seed $s > $D/seed_$s.log 2>&1 & pids+=($!); done
for p in "${pids[@]}"; do wait "$p"; done
echo "C0 seeds done $(date)"; grep -h "Error\|Traceback" $D/seed_*.log; $PY -u scripts/CITY_c0_testbed.py --out $D --merge > $D/merge.log 2>&1; tail -30 $D/merge.log
echo "Q4 panels start $(date)"; nice -n 12 $PY -u scripts/CITY_q4_corridor.py --out $Q --panels > $Q.panels.log 2>&1
pids=(); for s in 0 1 2; do nice -n 12 $PY -u scripts/CITY_q4_corridor.py --out $Q --seed $s > $Q.seed_$s.log 2>&1 & pids+=($!); done
for p in "${pids[@]}"; do wait "$p"; done
echo "Q4 seeds done $(date)"; grep -h "Error\|Traceback" $Q.seed_*.log; $PY -u scripts/CITY_q4_corridor.py --out $Q --merge > $Q.merge.log 2>&1; tail -16 $Q.merge.log
echo "queue end $(date)"
