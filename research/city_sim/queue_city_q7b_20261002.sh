#!/usr/bin/env bash
# City Q7b queue (02/10/2026 23:1x; PROTOCOL_CITY_Q7B_CONTRACT_20261002.md + Amendment 1 + Note): lanes t = 1, 2, 3 (L-ACT_t,
# RL-H_t, L-FT_t, then RL-J_t with L-ACT_t), plus L-FT_t0; then evaluations t = 0..3; report; dashboard.  nohup-launched.
cd /Users/phanan/cig-amf-main; PY=external_envs/city_runtime/bin/python; D=research/city_sim/q7b_contract_20261002; mkdir -p $D
Q="$PY -u scripts/CITY_q7b_contract.py --out $D --episodes 120"
echo "Q7b start $(date)"
nice -n 10 $Q --t 0 --train-fleet L-FT_t0 --against FT > $D/train_L-FT_t0.log 2>&1 &
for t in 1 2 3; do
  ( nice -n 10 $Q --t $t --train-fleet L-ACT_t$t > $D/train_L-ACT_t$t.log 2>&1
    nice -n 10 $Q --t $t --train-light RL-H_t$t > $D/train_RL-H_t$t.log 2>&1
    nice -n 10 $Q --t $t --train-fleet L-FT_t$t --against FT > $D/train_L-FT_t$t.log 2>&1
    [ -f $D/L-ACT_t$t.pt ] && nice -n 10 $Q --t $t --train-light RL-J_t$t --with-fleet $D/L-ACT_t$t.pt > $D/train_RL-J_t$t.log 2>&1
    echo "lane t$t trained $(date)" ) &
done
wait
for f in L-FT_t0 L-ACT_t1 RL-H_t1 L-FT_t1 RL-J_t1 L-ACT_t2 RL-H_t2 L-FT_t2 RL-J_t2 L-ACT_t3 RL-H_t3 L-FT_t3 RL-J_t3; do [ -f $D/$f.pt ] || echo "MISSING $f"; done
echo "eval start $(date)"
for t in 0 1 2 3; do nice -n 10 $Q --t $t --eval > $D/eval_t$t.log 2>&1 & done
wait
$Q --report > $D/report_stdout.txt 2>&1; tail -12 $D/report_stdout.txt
python3 scripts/DASH_build.py
echo "Q7b end $(date)"
