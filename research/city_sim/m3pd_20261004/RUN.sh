#!/usr/bin/env bash
# M3′-D (PROTOCOL_CITY_M3P_DIAG_20261004): 16 closed-loop cells + 16 shadows on the M3′ DEV panel (C11 records phases), KD-1, then 8 replay jobs, report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/m3pd_20261004
P=research/city_sim/spat_pilot_20261004/fleets_v11; S="100 101 102 103 104 200 201 202 203 204 205 206 207 208 209"; J=$D/jobs.txt; : > $J; mkdir -p $D/dev/tmp $D/replay/tmp
for k in 0 1; do for fl in s13 s113; do for c in 11 01 10 00; do F=${c:0:1}; M=${c:1:1}; REC=""; [ $c = 11 ] && REC="--record $D/rec/k${k}_${fl}/phases_s{seed}.npz"
  echo "C${c}_k${k}_${fl} --light RPC2:$k:receiver:$F:$M --fleet PL:$P/L11_${fl}_fleet.pt $REC" >> $J
  echo "C${c}_k${k}_${fl}_sh --light RPC2:$k:receiver:$F:$M --fleet SHADOW:$P/L11_${fl}_fleet.pt" >> $J; done; done; done
export PY D S; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || XPLAY_TMP=$PWD/$D/dev/tmp nice -n 5 $PY -u scripts/CITY_eval_m3p2.py "$@" --seeds $S --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
echo "closed loop done $(date)"
for k in 0 1; do for fl in s13 s113; do for m in withdraw keep; do [ -f $D/replay/${m}_k${k}_${fl}.json ] || XPLAY_TMP=$PWD/$D/replay/tmp nice -n 5 $PY -u scripts/CITY_eval_m3p2_replay.py --msg $m \
  --commits $D/dev/C11_k${k}_${fl}_m3p2.json --replay-dir $D/rec/k${k}_${fl} --fleet PL:$P/L11_${fl}_fleet.pt --seeds $S --tag ${m}_k${k}_${fl} --out $D/replay >> $D/replay/run.log 2>&1 &
done; done; done; wait; echo "replay done $(date)"; $PY scripts/CITY_m3p_diag_report.py; echo "M3pD done $(date)"
