#!/usr/bin/env bash
# SPaT pilot evaluation (PROTOCOL_CITY_SPAT_PILOT_20261004): STAGE=pilot -> SELECT 100-104 (eval_select); STAGE=confirm -> 420-429 (eval_confirm,
# only if GATE_PASS).  Comparators re-run in the same directory: always-SUMO, σ-family, GLOSA.  Run outside the spool (the spool is busy
# with training job 059).  Usage: RUN_spatp_eval.sh pilot|confirm
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=research/city_sim/spat_pilot_20261004; O=$D/fleets; ST=$1
if [ "$ST" = pilot ]; then E=$D/eval_select; S="100 101 102 103 104"; F="Bon_s13 Bon_s113 Boff_s13 Boff_s113"
else [ -f $D/eval_select/GATE_PASS ] || { echo "pilot gate not passed: confirmation not evaluated (registered)"; exit 0; }; E=$D/eval_confirm; S="420 421 422 423 424 425 426 427 428 429"
  F="Bon_s213 Bon_s313 Bon_s413 Bon_s513 Boff_s213 Boff_s313 Boff_s413 Boff_s513"; fi
mkdir -p $E/tmp
{ for f in ${F}; do echo "scripts/CITY_eval6.py --light FT --fleet P:$O/${f}_fleet.pt --seeds $S --tag $f"; done
  echo "scripts/CITY_eval6.py --light FT --fleet GLOSA --seeds $S --tag GLOSA_FT"
  echo "scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT"
  for sg in 0.0 0.1 0.2 0.3 0.4; do echo "scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT"; done; } |
  xargs -P 6 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$E"'/tmp nice -n 5 '"$PY"' -u "$@" --out '"$E"' >> '"$E"'/run.log 2>&1 || echo "FAIL $*"' sh
$PY scripts/CITY_spatp_report.py $ST
