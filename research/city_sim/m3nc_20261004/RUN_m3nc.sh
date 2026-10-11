#!/usr/bin/env bash
# M3-NC (PROTOCOL_CITY_M3_NEG_CONFIRM_20261004): traffic 510-529 (KN-4) -> checks KN-1..3 (t4, 510) -> 90 panel jobs (6 at a time) -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/m3nc_20261004; RN=scripts/CITY_f1a1_run.py
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; PV=research/city_sim/f1a1_20261004/prep; P=research/city_sim/spat_pilot_20261004/fleets_v11
mkdir -p $D/check/tmp $D/eval/tmp; echo "start $(date)"
if [ ! -f $D/check/traffic_generated ]; then
  for s in $(seq 510 529); do [ -f $G/rou_s$s.xml ] && { echo "KN-4 FAIL: $G/rou_s$s.xml existed"; exit 1; }; done
  for s in $(seq 510 529); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger \
    --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "KN-4 PASS $(date)" | tee $D/check/traffic_generated; fi
job() { # $1 out dir, $2 tag, $3 seeds, rest: script + args
  O=$1; T=$2; S=$3; shift 3; [ -f $O/$T.json ] && return 0; XPLAY_TMP=$PWD/$O/tmp nice -n 5 $PY -u $RN "$@" --seeds $S --tag $T --out $O >> $O/run.log 2>&1 || echo "FAIL $T"; }
spec() { # tag light fleet -> one job line for the panel / check
  t=$1; f=$2; case $3 in
    R) echo "R_t${t}_$f scripts/CITY_eval_m3.py --spat-arm none --light RL-H:$t --fleet PL:$P/L11_s${f}_fleet.pt";;
    WC5) echo "WC5_t${t}_$f scripts/CITY_eval_m3.py --spat-arm commit:$PV/prov_rlh${t}_cl.json --light M3WC:$t:5 --fleet PL:$P/L11_s${f}_fleet.pt";;
    WC5c) echo "WC5c_t${t}_$f scripts/CITY_eval_m3nc.py --spat-arm commitc:0.1:$PV/prov_rlh${t}_cl.json --light M3WC:$t:5 --fleet PL:$P/L11_s${f}_fleet.pt";;
    RPC) echo "RPC_t${t}_$f scripts/CITY_eval_m3p.py --light RPC:$t:receiver --fleet PL:$P/L11_s${f}_fleet.pt";;
    RPCsh) echo "RPCsh_t${t}_$f scripts/CITY_eval_m3p_shadow.py --light RPC:$t:receiver --fleet SHADOW:$P/L11_s${f}_fleet.pt";;
    WC5sig) echo "WC5sig_t${t} scripts/CITY_eval_m3.py --spat-arm none --light M3WC:$t:5 --base-sigma 0.3 --fleet L-ACT:0 --guard always";; esac; }
export -f job; export PY RN
{ spec 4 213 R; spec 4 313 R; spec 4 213 WC5; spec 4 213 WC5c; spec 4 213 RPC; spec 4 213 RPCsh; spec 4 x WC5sig; } | { while read T rest; do job $D/check $T 510 $rest & done; wait; }
$PY scripts/CITY_m3nc_check.py || { echo "M3-NC checks FAIL: stop"; exit 1; }
J=$D/eval/jobs.txt; : > $J
for t in 4 5 6 7 8; do spec $t 213 R | sed "s/^R_t${t}_213/R_t$t/" >> $J; spec $t x WC5sig >> $J
  for f in 213 313 413 513; do for a in WC5 RPC RPCsh WC5c; do spec $t $f $a >> $J; done; done; done
S="$(seq -s ' ' 510 529)"; export S D
xargs -P 6 -L 1 bash -c 'job $D/eval "$0" "$S" "$@"' < $J
echo "panel done $(date)"; $PY scripts/CITY_m3nc_report.py; echo "M3-NC done $(date)"
