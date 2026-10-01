#!/usr/bin/env bash
# F2-C downstream for the mixed-profile actor (PROTOCOL_E3_MIXACTOR_20260928.md, "Downstream: unchanged"), run AFTER the
# mix actor's training manifest exists.  It never trains an actor (RUN_marl_e3_resume_v3.sh would retrain a missing actor
# with the SCRATCH trainer and log the SCRATCH protocol hash, both wrong here).  Stages, each skipped when complete:
#   1. message use on development 501-508 (G1/G2 as in PROTOCOL_E3_PILOT §5, per seed);
#   2. continuation labels v3 (resumable in place): train t in {7,10,13,16,19,22}, 3 shards; select/dev t in {10,16,22};
#      then the key-level label audit (refuses on any defect);
#   3. selectors v1 (sel_nobid, sel_bid) and closed loop v1 direct (the original chain's stages);
#   4. the four-variant ablation (selector v2 + closed loop v3 on the pilot panel 901-916, RUN_marl_e3_ablation.sh);
#   5. the legal-vs-privileged diagnostic (selector v3, RUN_marl_e3_priv_diag.sh) and diagnostic v2;
#   6. side-by-side table against the reference prefix-trained actor (same measures; different actors cannot be paired
#      state by state, so no paired difference is claimed).
# Usage: bash scripts/RUN_marl_e3_mix_downstream.sh <mix actor dir> <reference actor dir>
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python; WD="$PY scripts/run_with_watchdog.py"
D="${1:?mix actor dir}"; REF="${2:?reference actor dir}"; CK="$D/ckpt_best.pt"
[ -f "$D/manifest.json" ] || { echo "refusing: $D has no training manifest (the mix actor is not finished)"; exit 2; }
python3 -c "import json,sys; c=json.load(open(sys.argv[1])); assert c.get('p_mix', 0) > 0, 'not a mixed-profile actor'" "$D/config.json"
PROTO=research/marl_budget/PROTOCOL_E3_MIXACTOR_20260928.md
echo "mix downstream: protocol sha256 $(shasum -a 256 $PROTO | cut -d' ' -f1) $(date)" | tee -a "$D/chain.log"
[ -f "$D/msguse/manifest.json" ] || $WD --log "$D/msguse.log" --out "$D/msguse" --stall 1800 -- "$PY" -u scripts/MARL_e3_message_use.py --ckpt "$CK" --out "$D/msguse" --seeds $(seq -s ' ' 501 508)
PIDS=""
for k in 0 1 2; do L="$D/labels_train_$k"
  [ -f "$L/manifest.json" ] || { $WD --log "$L.log" --stall 1800 --retries 50 -- "$PY" -u scripts/MARL_e3_continuation_labels_v3.py --ckpt "$CK" --out "$L" --split train --snaps 7 10 13 16 19 22 --limit 0 --shard $k --nshards 3 & PIDS="$PIDS $!"; }
done
for sp in select dev; do L="$D/labels_$sp"
  [ -f "$L/manifest.json" ] || { $WD --log "$L.log" --stall 1800 --retries 50 -- "$PY" -u scripts/MARL_e3_continuation_labels_v3.py --ckpt "$CK" --out "$L" --split $sp --snaps 10 16 22 --limit 0 & PIDS="$PIDS $!"; }
done
rc=0; for p in $PIDS; do wait $p || rc=$?; done; [ $rc = 0 ] || { echo "a label job failed ($rc)"; exit $rc; }
python3 scripts/MARL_e3_labels_audit.py "$D/labels_*" --out "$D/labels_audit.json" > "$D/labels_audit.txt" || { echo "label audit found a defect"; cat "$D/labels_audit.txt"; exit 2; }
PIDS=""
for s in 0 1 2; do
  [ -f "$D/selectors/job_sel_nobid_s$s.json" ] || { "$PY" -u scripts/MARL_e3_selector_train.py --train "$D/labels_train_*" --select "$D/labels_select" --dev "$D/labels_dev" --out "$D/selectors" --name sel_nobid --seed $s --epochs 40 > "$D/sel_nobid_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  [ -f "$D/selectors/job_sel_bid_s$s.json" ] || { "$PY" -u scripts/MARL_e3_selector_train.py --train "$D/labels_train_*" --select "$D/labels_select" --dev "$D/labels_dev" --out "$D/selectors" --name sel_bid --bid --seed $s --epochs 40 > "$D/sel_bid_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
done
for p in $PIDS; do wait $p; done
[ -f "$D/cl_direct/manifest.json" ] || $WD --log "$D/cl_direct.log" --out "$D/cl_direct" --stall 1800 -- "$PY" -u scripts/MARL_e3_closed_loop.py --actor "$CK" --selectors "$D/selectors" --names sel_nobid sel_bid --policy direct --mp2 --out "$D/cl_direct" --traffic-seeds $(seq -s ' ' 901 916)
bash scripts/RUN_marl_e3_ablation.sh "$D"
bash scripts/RUN_marl_e3_priv_diag.sh "$D"
"$PY" scripts/MARL_e3_selector_diag_v2.py --actor-dir "$D" --selectors selectors_v2 --out "$D/selectors_v2_diag.json" > "$D/selectors_v2_diag.txt" 2>&1
python3 - "$D" "$REF" <<'EOF' | tee "$D/mix_vs_reference.txt"
import json, sys
from pathlib import Path
from collections import defaultdict
import numpy as np
def cl(d):
    rows = json.loads((Path(d) / 'cl_v3_direct/rows.json').read_text()); per = defaultdict(lambda: defaultdict(list))
    for r in rows: per[r['method'].split('/')[0]][r['episode']].append(r['queue_sum'])
    eps = sorted(per['prefix']); pq = {e: per['prefix'][e][0] for e in eps}
    return {m: round(float(np.mean([100 * (np.mean(v[e]) - pq[e]) / pq[e] for e in eps])), 2) for m, v in per.items() if m != 'prefix'}
for name, d in (('mixed-profile actor', sys.argv[1]), ('reference (prefix-trained)', sys.argv[2])):
    g = json.loads((Path(d) / 'msguse/report.json').read_text()); dg = json.loads((Path(d) / 'selectors_v3_diag.json').read_text())
    legal = [dg[k]['direct']['dev'] for k in dg if k.startswith('legal_bid_resp')]; priv = [dg[k]['direct']['dev'] for k in dg if k.startswith('priv_only')]
    print(f'== {name}: {d}')
    print(f'   MP2 vs actor {g["mp2_vs_actual_pct"]["mean"]:+.1f}%, none vs actual {g["none_vs_actual_pct"]["mean"]:+.1f}% {g["none_vs_actual_pct"]["ci95"]}')
    print(f'   closed loop vs its prefix (901-916, +84 B): {cl(d)}')
    for lab, L in (('legal bid+head (v3)', legal), ('privileged (v3)', priv)):
        print(f'   {lab}: realised dev gain {np.mean([x["realised_gain"] for x in L]):+.2f}, edit {np.mean([x["edit_rate"] for x in L]):.2f}, '
              f'harm|edit {np.nanmean([x["harmful_edit_rate"] if x["harmful_edit_rate"] is not None else np.nan for x in L]):.2f}, '
              f'pair acc {np.mean([x["pair_order_accuracy"] for x in L]):.3f}, oracle {L[0]["oracle_best"]:.1f}')
EOF
echo "mix downstream done $D $(date)"
