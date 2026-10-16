#!/usr/bin/env bash
# W21-G / W21-H (PROTOCOL_CITY_WAVE21_20261015): Midtown, MT-E setting, fleet s1413, days 0-4, AH t34-38 and B2D t59-63.
#  G: replay on the actrest base (CITY_w21_mt_replay.py): KH-1 on the first light-day, then SIG / ORC on R's schedule (W21-C SHADOWg traces)
#     and on the forecast run's schedule (SERVEg traces); KH-1 on every light-day in the report.
#  H: learned greens capped at 20 s (MT_MAX_G) with a cap-aware provider (MT_SPAT_CAP): LGc / Rc / SVc.
# Then CITY_w21gh_report.py.  LANES (default 6).  SMOKE=1: t34 and t60, day 0, --smoke, replaying the W21-C smoke traces, into .../smoke_gh.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; FL=research/city_sim/w15_20261007/fresh3/fleets/L11_s1413_fleet.pt; LANES=${LANES:-6}
if [ "${SMOKE:-0}" = 1 ]; then C=research/city_sim/w21_20261015/smoke_c; E=${W21GH_DIR:-research/city_sim/w21_20261015/smoke_gh}; LT="34 60"; DAYS="0"; SM="--smoke"
else C=research/city_sim/w21_20261015/midtown_diag; E=${W21GH_DIR:-research/city_sim/w21_20261015/midtown_gh}; LT="34 35 36 37 38 59 60 61 62 63"; DAYS="0 1 2 3 4"; SM=""; fi
mkdir -p $E; export PY E SM DAYS; export M="$PY -u scripts/DEMO_midtown.py scripts/CITY_w21_mt_replay.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"
echo "W21-G/H start $(date); dir $E; lanes $LANES"
echo "sources: $(shasum -a 256 scripts/CITY_w21_mt_replay.py scripts/DEMO_midtown.py scripts/CITY_eval4.py scripts/CITY_m3_headroom.py scripts/CITY_eval_f1.py scripts/CITY_eval_n4.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
run() { xargs -P $LANES -L 1 bash -c 'T=$0; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0
  nice -n 5 env $EXTRA_ENV $M "$@" --seeds $DAYS $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $1
  bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
export EXTRA_ENV=""
# G: KH-1 first
K1=$(echo $LT | cut -d' ' -f1); J=$E/jobs_kh1.txt
echo "SIGR_t$K1 scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$K1 --fleet PL:$FL --replay-dir $C/rec/SHADOWg_t$K1" > $J; run $J
KH=$($PY - "$E" "$C" "$K1" "$DAYS" <<'PY'
import json, sys
E, C, k, days = sys.argv[1], sys.argv[2], sys.argv[3], [int(x) for x in sys.argv[4].split()]
a = {r['seed']: r for r in json.load(open(f'{E}/SIGR_t{k}.json'))['rows']}; b = {r['seed']: r for r in json.load(open(f'{C}/SHADOWg_t{k}.json'))['rows']}
F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports', 'unfinished', 'action_digest')
bad = [(s, f, a[s][f], b[s][f]) for s in days for f in F if a[s][f] != b[s][f]]
print('PASS' if not bad else 'FAIL ' + str(bad[:4]))
PY
); echo "KH-1 (replay of R's schedule with the fleet without SPaT reproduces R, t$K1): $KH" | tee $E/kh1.txt
if [ "${KH%% *}" = PASS ]; then J=$E/jobs_g.txt; : > $J
  for k in $LT; do for sch in R S; do src=SHADOWg; [ $sch = S ] && src=SERVEg; F="--light RL-H:$k --fleet PL:$FL --replay-dir $C/rec/${src}_t$k"
    [ "$sch$k" = "R$K1" ] || echo "SIG${sch}_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "ORC${sch}_t$k scripts/CITY_m3_headroom.py $F" >> $J; done; done
  echo "G: $(wc -l < $J) jobs"; run $J || echo "G incomplete (listed above)"; echo "G done $(date)"
else echo "G skipped: KH-1 not passed"; fi
# H: capped greens, cap-aware provider
export EXTRA_ENV="MT_MAX_G=20 MT_SPAT_CAP=20"; J=$E/jobs_h.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$FL"
  echo "LGc_t$k scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
  echo "Rc_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  echo "SVc_t$k scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt $F" >> $J; done
echo "H: $(wc -l < $J) jobs"; run $J || echo "H incomplete (listed above)"; echo "H done $(date)"
W21_SMOKE=${SMOKE:-0} $PY scripts/CITY_w21gh_report.py $E $C "$LT" "$DAYS" || { echo "report FAIL"; exit 1; }
echo "W21-G/H done $(date)"
