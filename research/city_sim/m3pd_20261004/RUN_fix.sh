#!/usr/bin/env bash
# M3′-D fix (C-92): the same jobs as RUN.sh, job lines built WITHOUT trailing blanks; existing outputs are skipped; 4 parallel; then replay + report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/m3pd_20261004
P=research/city_sim/spat_pilot_20261004/fleets_v11; S="100 101 102 103 104 200 201 202 203 204 205 206 207 208 209"; J=$D/jobs_fix.txt; : > $J; mkdir -p $D/dev/tmp $D/replay/tmp
for k in 0 1; do for fl in s13 s113; do for c in 11 01 10 00; do F=${c:0:1}; M=${c:1:1}
  if [ $c = 11 ]; then echo "C${c}_k${k}_${fl} --light RPC2:$k:receiver:$F:$M --fleet PL:$P/L11_${fl}_fleet.pt --record $D/rec/k${k}_${fl}/phases_s{seed}.npz" >> $J
  else echo "C${c}_k${k}_${fl} --light RPC2:$k:receiver:$F:$M --fleet PL:$P/L11_${fl}_fleet.pt" >> $J; fi
  echo "C${c}_k${k}_${fl}_sh --light RPC2:$k:receiver:$F:$M --fleet SHADOW:$P/L11_${fl}_fleet.pt" >> $J; done; done; done
grep -c ' $' $J | xargs -I{} sh -c '[ {} -eq 0 ] || { echo "trailing blanks remain: stop"; exit 1; }' || exit 1
export PY D S; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || XPLAY_TMP=$PWD/$D/dev/tmp nice -n 5 $PY -u scripts/CITY_eval_m3p2.py "$@" --seeds $S --tag $T --out $D/dev >> $D/dev/run_fix.log 2>&1 || echo "FAIL $T"' < $J
n=$(ls $D/dev/C*_m3p2.json | wc -l); echo "closed-loop sidecars $n / 32 $(date)"; [ "$n" -eq 32 ] || { echo "missing cells: stop"; exit 1; }
R2=$D/jobs_replay.txt; : > $R2; for k in 0 1; do for fl in s13 s113; do for m in withdraw keep; do echo "${m}_k${k}_${fl} $m $D/dev/C11_k${k}_${fl}_m3p2.json $D/rec/k${k}_${fl} PL:$P/L11_${fl}_fleet.pt" >> $R2; done; done; done
xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/replay/$T.json ] || XPLAY_TMP=$PWD/$D/replay/tmp nice -n 5 $PY -u scripts/CITY_eval_m3p2_replay.py --msg $1 --commits $2 --replay-dir $3 --fleet $4 --seeds $S --tag $T --out $D/replay >> $D/replay/run.log 2>&1 || echo "FAIL $T"' < $R2
echo "replay done $(date)"; $PY scripts/CITY_m3p_diag_report.py; echo "M3pD fix done $(date)"
