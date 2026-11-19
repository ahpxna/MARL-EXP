#!/usr/bin/env bash
# W21-B (PROTOCOL_CITY_WAVE21_20261015): the pair R / SV on the full Midtown map in the MT-E setting (DEMO_midtown.py, MT_NET=midtown_full,
# MT_BASE=actrest, Krauss drivers, random demand days 0-4), stop-thresholded family AH (W19 t34-t38; registered fallback RMP, W20 t94-t98)
# against the control B2D (W19 t59-t63, MT-E's family); fleets FRESH3 s1413-s1713; each light's grid forecaster adapted by DEMO_midtown.
# Steps: ACT + LGar of the threshold family -> gate G21-B0 (no gridlock: <= 20 teleports and <= 20 unfinished per run; else the fallback)
# -> R / SV of both families -> KW21-B1 (B2D SV and ACT equal MT-E's MTF_BGar / MTF_ACT rows) -> CITY_w21_report.py b.
# A failed cell does not stop the others; the report refuses incomplete panels.  LANES (default 3) parallel processes.
# SMOKE=1: one light per family, fleet s1413, day 0, --smoke, into W21B_DIR (default .../w21_20261015/smoke_b); KW21-B1 skipped.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; W20=research/city_sim/w20_20261009; F3=research/city_sim/w15_20261007/fresh3/fleets
MTE=research/city_sim/midtown_transfer_20261010/eval_full; LANES=${LANES:-3}
if [ "${SMOKE:-0}" = 1 ]; then E=${W21B_DIR:-research/city_sim/w21_20261015/smoke_b}; SL="0"; FS="1413"; DAYS="0"; SM="--smoke"
else E=${W21B_DIR:-research/city_sim/w21_20261015/midtown}; SL="0 1 2 3 4"; FS="1413 1513 1613 1713"; DAYS="0 1 2 3 4"; SM=""; fi
mkdir -p $E; RUNM="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"
echo "W21-B start $(date); dir $E; lanes $LANES"
echo "sources: $(shasum -a 256 scripts/DEMO_midtown.py scripts/CITY_w9_run.py scripts/CITY_w20_run.py scripts/CITY_w20_bench.py scripts/CITY_w19_run.py scripts/CITY_w19_obs.py scripts/CITY_eval_n4.py scripts/CITY_eval_f1.py scripts/CITY_eval6_v11.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
k0() { case $1 in AH) echo 34;; RMP) echo 94;; B2D) echo 59;; esac; }
pdir() { case $1 in RMP) echo $W20;; *) echo $W19;; esac; }
lg_jobs() { for j in $SL; do k=$(( $(k0 $1) + j )); echo "MTW_LGar_t$k scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always"; done; }
pair_jobs() { P=$(pdir $1); for j in $SL; do k=$(( $(k0 $1) + j )); for s in $FS; do F="--light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
  echo "MTW_R_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none $F"
  echo "MTW_SV_t${k}_s$s scripts/CITY_eval_n4.py --n4 0.1:hyb:$P/prep/prov_rlh${k}_cl.json:$P/cmodel/n2_k$k.pt $F"; done; done; }
export PY E SM DAYS RUNM
run() { xargs -P $LANES -L 1 bash -c 'T=$0; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0
  nice -n 5 $RUNM "$@" --seeds $DAYS $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $1
  bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
gate() { $PY - "$E" "$1" "$SL" "${SMOKE:-0}" <<'PY'
import json, sys
E, f, SL = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split()]; k0 = {'AH': 34, 'RMP': 94}[f]
R = [r for j in SL for r in json.load(open(f'{E}/MTW_LGar_t{k0 + j}.json'))['rows']]; A = json.load(open(f'{E}/MTW_ACT.json'))['rows']
tp, un = sum(r['teleports'] for r in R) / len(R), sum(r['unfinished'] for r in R) / len(R); ok = tp <= 20 and un <= 20
if sys.argv[4] == '1':
    print('(smoke: truncated episodes leave trips unfinished; gate printed, not enforced)'); ok = True
act = {r['seed']: r['timeloss'] for r in A}; d = [r['timeloss'] - act[r['seed']] for r in R]
print(f'G21-B0[{f}]: LGar teleports/run {tp:.1f}, unfinished/run {un:.1f} (limit 20 / 20) -> {"PASS" if ok else "FAIL"}; '
      f'city TL LGar {sum(r["timeloss"] for r in R) / len(R):.1f} vs ACT {sum(act.values()) / len(act):.1f} s/veh (mean paired difference {sum(d) / len(d):+.1f}; descriptive)')
sys.exit(0 if ok else 1)
PY
}
# 1. gate: ACT and the threshold family's lights alone (all human)
THR=""
for f in AH RMP; do J=$E/jobs_gate_$f.txt; { echo "MTW_ACT scripts/CITY_eval6_v11.py --light ACT --fleet L-ACT:0 --guard always"; lg_jobs $f; } > $J
  run $J || { echo "gate rows incomplete for $f: stop"; exit 1; }
  if gate $f | tee -a $E/gate.txt; then THR=$f; break; fi
  echo "threshold family $f gridlocks or fails the gate; registered fallback next"; done
[ -n "$THR" ] || { echo "G21-B0: no stop-thresholded family runs Midtown without gridlock (AH, RMP): report and stop"; exit 2; }
echo "threshold family: $THR $(date)"
# 2. the pair for the threshold family and the control B2D
J=$E/jobs_pairs.txt; { pair_jobs $THR; pair_jobs B2D; } > $J; echo "pair rows: $(wc -l < $J) jobs x $(echo $DAYS | wc -w) days"
run $J || echo "some pair rows incomplete (listed above)"
# 3. KW21-B1: reproduction of MT-E with the current code
if [ "${SMOKE:-0}" != 1 ]; then $PY - "$E" "$MTE" <<'PY' | tee $E/kw21_b1.txt
import json, sys
E, M = sys.argv[1], sys.argv[2]; F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'waiting', 'teleports', 'unfinished', 'action_digest')
pairs = [('MTW_ACT', 'MTF_ACT')] + [(f'MTW_SV_t{k}_s{s}', f'MTF_BGar_t{k}_s{s}') for k in range(59, 64) for s in (1413, 1513, 1613, 1713)]
bad = []; n = 0
for a, b in pairs:
    try:
        A, B = json.load(open(f'{E}/{a}.json')), json.load(open(f'{M}/{b}.json'))
    except FileNotFoundError as e:
        bad.append(f'{a}: missing ({e.filename})'); continue
    ra, rb = {r['seed']: r for r in A['rows']}, {r['seed']: r for r in B['rows']}
    for s in sorted(rb):
        n += 1; diff = [k for k in F if ra.get(s, {}).get(k) != rb[s].get(k)]
        if diff:
            bad.append(f'{a} day {s}: {diff} (src {A.get("source_sha256", "")[:12]} vs {B.get("source_sha256", "")[:12]})')
print(f'KW21-B1: {n - len(bad)} of {n} (row, day) pairs identical to MT-E on {", ".join(F)}' + ('' if not bad else ' — MISMATCH:\n  ' + '\n  '.join(bad[:30])))
print('KW21-B1 PASS' if not bad else 'KW21-B1 FAIL (reported; the registered reading uses the W21 rows)')
PY
else echo "KW21-B1 skipped in smoke"; fi
W21_SMOKE=${SMOKE:-0} W21_THR=$THR $PY scripts/CITY_w21_report.py b $E || { echo "report FAIL"; exit 1; }
echo "W21-B done $(date)"
