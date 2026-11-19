#!/usr/bin/env bash
# W21-L0 (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-L0): the untrained W21-L init (zero-residual actor = GLOSA-L∘σ*) under the SV
# service on the full Midtown map -> KW21-L0a (actor last layer exactly zero), KW21-L0b (four seeds identical on t59) -> CITY_w21l0_report.py.
# ALL=1: all four seeds on every light (the registered fallback if KW21-L0b fails).  SMOKE=1: s1413, t59, day 0, --smoke, into .../smoke_l0.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full W13_AB=0:0
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; B=research/city_sim/w21_20261015/midtown; L=research/city_sim/w21_20261015/midtown_fleet
if [ "${SMOKE:-0}" = 1 ]; then E=${W21L0_DIR:-research/city_sim/w21_20261015/smoke_l0}; FS="1413"; LB="59"; LA=""; DAYS="0"; SM="--smoke"
else E=${W21L0_DIR:-research/city_sim/w21_20261015/midtown_rule}; FS="1413 1513 1613 1713"; LB="59 60 61 62 63"; LA="34 35 36 37 38"; DAYS="0 1 2 3 4"; SM=""; fi
mkdir -p $E/fleets; echo "W21-L0 start $(date); dir $E; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w21_train_fleet_mt.py scripts/CITY_fleet_v11.py scripts/CITY_fleet_v9.py scripts/CITY_eval_n4.py scripts/CITY_eval6_v11.py scripts/DEMO_midtown.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
# 1. the untrained init, saved by the W21-L trainer (0 episodes)
i=0; for s in $FS; do k=$((59 + i)); i=$((i + 1))
  [ -f $E/fleets/MTL0_s${s}_fleet.pt ] || W13_N4=0.1:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt $PY -u scripts/DEMO_midtown.py scripts/CITY_w20_run.py scripts/CITY_w21_train_fleet_mt.py --seed $s --light-k $k --episodes 0 --name MTL0_s$s --out $E/fleets >> $E/fleets/init_s$s.out 2>&1 || { echo "init FAILED s$s"; tail -3 $E/fleets/init_s$s.out; exit 1; }
done
$PY - $E/fleets "$FS" <<'PY' || exit 1
import sys, torch
ok = True
for s in sys.argv[2].split():
    d = torch.load(f'{sys.argv[1]}/MTL0_s{s}_fleet.pt', weights_only=False); n = d['net']; w, b = n.pi[4].weight, n.pi[4].bias
    z = bool((w == 0).all() and (b == 0).all()); ok &= z and d['episodes'] == 0
    print(f'KW21-L0a s{s}: episodes {d["episodes"]}, actor last layer |w|max {w.abs().max().item():.3g}, |b|max {b.abs().max().item():.3g} -> {"PASS" if z else "FAIL"}')
sys.exit(0 if ok else 1)
PY
# 2. evaluation
export PY E SM DAYS; export M="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"
run() { xargs -P ${LANES:-6} -L 1 bash -c 'T=$0; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0
  nice -n 5 $M "$@" --seeds $DAYS $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $1
  bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
J=$E/jobs_eval.txt; : > $J; F1=$(echo $FS | cut -d' ' -f1)
for k in $LB $LA; do if [ "$k" = 59 ] || [ "${ALL:-0}" = 1 ]; then SS="$FS"; else SS="$F1"; fi
  for s in $SS; do echo "MTL0_SV_t${k}_s$s scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$E/fleets/MTL0_s${s}_fleet.pt" >> $J; done; done
echo "evaluation: $(wc -l < $J) jobs x $(echo $DAYS | wc -w) days"; run $J || echo "evaluation incomplete (listed above)"; echo "evaluation done $(date)"
W21_SMOKE=${SMOKE:-0} $PY scripts/CITY_w21l0_report.py $E $B $L "$FS" "$LB" "$LA" "$DAYS" || { echo "report FAIL"; exit 1; }
echo "W21-L0 done $(date)"
