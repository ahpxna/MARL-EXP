#!/usr/bin/env bash
# PROTOCOL_AGE_ROLE_PROBE_20261002.md, MARL part: relay6Cage at iid, relayCK1 at K = 1, seeds 0-4, dev 901-904 x 8/16.
cd "$(dirname "$0")/../../.."; export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_age_role_probe_20261002
for s in "$@"; do
  external_envs/runtime/bin/python -u scripts/MARL_e3_age_role_probe.py --relay $D/relay6Cage_st_s$s/ckpt_best.pt --tag relay6Cage_st_s$s --K 0 --out $P/relay6Cage_st_s$s.json
  external_envs/runtime/bin/python -u scripts/MARL_e3_age_role_probe.py --relay $D/relayCK1_st_s$s/ckpt_best.pt --tag relayCK1_st_s$s --K 1 --out $P/relayCK1_st_s$s.json
done
