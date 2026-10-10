# 050 P2 mid-run handoff (TEST traffic) — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md
cd /Users/phanan/cig-amf-main
{ for t in 0 1 2 3; do for f in 0 1 2 3; do for g in none fallback green+oos; do
      echo "--light ACTP --swap-at 1800 --swap-light RL-H:$t --fleet L-ACT:$f --guard $g --delay-trace --seeds 200 201 202 203 204 205 206 207 208 209 --tag L_RLH${t}_F${f}_$(echo $g | tr '+' 'P')"; done
    echo "--light ACTP --swap-at 1800 --swap-light RL-H:$t --swap-fleet L-RLH:$t --fleet L-ACT:$f --delay-trace --seeds 200 201 202 203 204 205 206 207 208 209 --tag S_RLH${t}_F${f}"; done; done
  for f in 0 1 2 3; do echo "--light ACTP --swap-at 1800 --swap-fleet L-RLH:$f --fleet L-ACT:$f --delay-trace --seeds 200 201 202 203 204 205 206 207 208 209 --tag F_F$f"
    for g in none green+oos; do echo "--light ACTP --fleet L-ACT:$f --guard $g --delay-trace --seeds 200 201 202 203 204 205 206 207 208 209 --tag B_F${f}_$(echo $g | tr '+' 'P')"; done; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/050
