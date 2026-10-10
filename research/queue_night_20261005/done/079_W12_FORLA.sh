#!/usr/bin/env bash
# W12-1c (PROTOCOL_CITY_WAVE12_20261006, A1): FoRL (kappa -0.25) and PPO-0 (kappa 0) retrained with the authors' reward scale (--reward authors),
# seeds 1-5, 200 ep -> KA-1 -> R_FA, FORLA_SP (provider v2), HUM_FA, R_P0A, HUM_P0A on fresh grid4 860-879 -> report.
# SMOKE=1: 2 x 300-s episodes, s1 / s213, seed 860, 600 s, into W12_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W12_DIR:-research/city_sim/w12_20261006/forla}; mkdir -p $D/lights $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
P=research/city_sim/spat_pilot_20261004/fleets_v11; RUN="$PY -u scripts/CITY_f1a1_run.py"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; EP=2; LS="1"; FLS="s213"; CS="860"; else SM=""; EP=200; LS="1 2 3 4 5"; FLS="s213 s313 s413 s513"; CS="$(seq -s ' ' 860 879)"; fi
[ -f research/city_sim/demand/grid4/CONF860_generated ] || { echo "KW12-0 FAIL"; exit 1; }
echo "W12-FORLA start $(date)"
# KA-1: authors' reward magnitude vs the port's on one smoke episode with an untrained net (same seed)
$PY - <<PYEOF || { echo "KA-1 FAIL: stop"; exit 1; }
import sys, numpy as np; sys.path.insert(0, '.')
import scripts.CITY_forl as FO
m = {}
for mode in ('port', 'authors'):
    FO.REWARD = mode; net = FO.Net(); info = FO.NetInfo(FO.Q7.NET_S); L = FO.LightFoRL(info, net, train=True, seed=7)
    FO.run_episode(FO.Q7.NET_S, FO.Q7.ROU.format(0), 0, L, None, end=600)
    m[mode] = float(np.mean([x['r_env'] for tr in L.traj.values() for x in tr if x['r_env'] is not None]))
ratio = m['authors'] / m['port']; print('KA-1 mean r_env port', round(m['port'], 4), 'authors', round(m['authors'], 3), 'ratio', round(ratio, 1))
assert 10 <= ratio <= 200, ratio
PYEOF
for s in $LS; do
  [ -f $D/lights/FORLA_s$s.pt ] || nice -n 5 $PY -u scripts/CITY_forl.py --reward authors --seed $s --episodes $EP --name FORLA_s$s --out $D/lights $SM > $D/lights/train_f$s.out 2>&1 &
  [ -f $D/lights/PPO0A_s$s.pt ] || nice -n 5 $PY -u scripts/CITY_forl.py --reward authors --kappa 0 --seed $s --episodes $EP --name PPO0A_s$s --out $D/lights $SM > $D/lights/train_p$s.out 2>&1 &
done; wait
for s in $LS; do for n in FORLA PPO0A; do [ -f $D/lights/${n}_s$s.pt ] || { echo "training failed $n s$s"; exit 1; }; done; done; echo "lights done $(date)"
$PY -c "import torch;d=torch.load('$D/lights/FORLA_s1.pt',weights_only=False);e=torch.load('$D/lights/PPO0A_s1.pt',weights_only=False);print('ckpt', d['reward'], d['kappa'], e['reward'], e['kappa']);assert d['reward']==e['reward']=='authors' and d['kappa']==-0.25 and e['kappa']==0.0" || { echo "checkpoint metadata FAIL"; exit 1; }
J=$D/conf_jobs.txt; : > $J
for s in $LS; do
  echo "HUM_FA_s$s scripts/CITY_eval_forl.py --forl-spat off --light FORL:$D/lights/FORLA_s$s.pt --fleet human" >> $J
  echo "HUM_P0A_s$s scripts/CITY_eval_forl.py --forl-spat off --light FORL:$D/lights/PPO0A_s$s.pt --fleet human" >> $J
  for fl in $FLS; do F="--fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_FA_s${s}_${fl} scripts/CITY_eval_forl.py --forl-spat off --light FORL:$D/lights/FORLA_s$s.pt $F" >> $J
    echo "FORLA_SP_s${s}_${fl} scripts/CITY_eval_forl.py --forl-spat on --light FORL:$D/lights/FORLA_s$s.pt $F" >> $J
    echo "R_P0A_s${s}_${fl} scripts/CITY_eval_forl.py --forl-spat off --light FORL:$D/lights/PPO0A_s$s.pt $F" >> $J; done; done
export PY D RUN SM SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "evaluation failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W12_SMOKE=$D W12_SEED=860 $PY scripts/CITY_w12_forla_report.py; else $PY scripts/CITY_w12_forla_report.py; fi || exit 1; echo "W12-FORLA done $(date)"
