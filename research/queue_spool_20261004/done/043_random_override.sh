# 055 matched-rate random override (Amendment W3 §5): RL-H_t x L-ACT_t' x random:0.046 / random:0.45, SELECT
cd /Users/phanan/cig-amf-main
{ for t in 0 1 2 3; do for f in 0 1 2 3; do for P in 0.046 0.45; do echo "--light RL-H:$t --fleet L-ACT:$f --guard random:$P --seeds 100 101 102 103 104 --tag RLH${t}_F${f}_rand$P"; done; done; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/055
