#!/usr/bin/env bash
# W21-I / W21-J / W21-K (PROTOCOL_CITY_WAVE21_20261015): Midtown, MT-E setting, fleet s1413, days 0-4, AH t34-38 and B2D t59-63.
#  J: PRB_R / PRB_SV with the read-only per-edge-length probe (CITY_w21_glide_probe.py, W21_PROBE=1)
#  I: RELs / RELl (glides released on edges < / >= 100 m), then RELr (random release at RELs's pooled released share per family)
#  K: BIS (TSI-G) for AH
# Then CITY_w21ijk_report.py.  LANES (default 6).  SMOKE=1: t34 and t60, day 0, --smoke, into .../smoke_ijk.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; FL=research/city_sim/w15_20261007/fresh3/fleets/L11_s1413_fleet.pt; LANES=${LANES:-6}
if [ "${SMOKE:-0}" = 1 ]; then C=research/city_sim/w21_20261015/smoke_c; E=${W21IJK_DIR:-research/city_sim/w21_20261015/smoke_ijk}; LA="34"; LB="60"; DAYS="0"; SM="--smoke"
else C=research/city_sim/w21_20261015/midtown_diag; E=${W21IJK_DIR:-research/city_sim/w21_20261015/midtown_ijk}; LA="34 35 36 37 38"; LB="59 60 61 62 63"; DAYS="0 1 2 3 4"; SM=""; fi
mkdir -p $E; export PY E SM DAYS; export M="$PY -u scripts/DEMO_midtown.py scripts/CITY_w21_glide_probe.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"
echo "W21-I/J/K start $(date); dir $E; lanes $LANES; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w21_glide_probe.py scripts/DEMO_midtown.py scripts/CITY_eval_n4.py scripts/CITY_eval_f1.py scripts/CITY_w20_bench.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
run() { xargs -P $LANES -L 1 bash -c 'T=$0; V=$1; shift; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0
  nice -n 5 env $(echo $V | tr , " ") $M "$@" --seeds $DAYS $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $1
  bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
N4() { echo "--n4 0.1:hyb:$W19/prep/prov_rlh$1_cl.json:$W19/cmodel/n2_k$1.pt"; }
J=$E/jobs_1.txt; : > $J
for k in $LA $LB; do F="--light RL-H:$k --fleet PL:$FL"
  echo "PRB_R_t$k W21_REL=none,W21_PROBE=1 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  echo "PRB_SV_t$k W21_REL=none,W21_PROBE=1 scripts/CITY_eval_n4.py $(N4 $k) $F" >> $J
  echo "RELs_t$k W21_REL=short:100,W21_PROBE=0 scripts/CITY_eval_n4.py $(N4 $k) $F" >> $J
  echo "RELl_t$k W21_REL=long:100,W21_PROBE=0 scripts/CITY_eval_n4.py $(N4 $k) $F" >> $J; done
for k in $LA; do echo "BIS_t$k W21_REL=none,W21_PROBE=0 scripts/CITY_eval_n4.py $(N4 $k) --light RL-H:$k --fleet PL:$FL --light-obs bis" >> $J; done
echo "stage 1: $(wc -l < $J) jobs x $(echo $DAYS | wc -w) days"; run $J || echo "stage 1 incomplete (listed above)"; echo "stage 1 done $(date)"
# matched rate per family from RELs
PA=$($PY -c "
import json, sys
E, ks = '$E', [int(x) for x in '$LA'.split()]
g = r = 0
for k in ks:
    for x in json.load(open(f'{E}/RELs_t{k}.json'))['rows']: g += x['w21_glide_s']; r += x['w21_released_s']
print(f'{r / max(1, g):.4f}')"); PB=$($PY -c "
import json
E, ks = '$E', [int(x) for x in '$LB'.split()]
g = r = 0
for k in ks:
    for x in json.load(open(f'{E}/RELs_t{k}.json'))['rows']: g += x['w21_glide_s']; r += x['w21_released_s']
print(f'{r / max(1, g):.4f}')"); echo "matched random release share: AH $PA, B2D $PB" | tee $E/matched_share.txt
J=$E/jobs_2.txt; : > $J
for k in $LA; do echo "RELr_t$k W21_REL=random:$PA,W21_PROBE=0 scripts/CITY_eval_n4.py $(N4 $k) --light RL-H:$k --fleet PL:$FL" >> $J; done
for k in $LB; do echo "RELr_t$k W21_REL=random:$PB,W21_PROBE=0 scripts/CITY_eval_n4.py $(N4 $k) --light RL-H:$k --fleet PL:$FL" >> $J; done
run $J || echo "stage 2 incomplete (listed above)"; echo "stage 2 done $(date)"
W21_SMOKE=${SMOKE:-0} $PY scripts/CITY_w21ijk_report.py $E $C "$LA" "$LB" "$DAYS" || { echo "report FAIL"; exit 1; }
echo "W21-I/J/K done $(date)"
