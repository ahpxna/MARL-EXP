#!/usr/bin/env bash
# Handoff F1 decision for the dense-label round (self-audit L-21/L-22/L-31/L-32; independent recheck P1), run AFTER every
# dense label directory is complete.  The REGISTERED analysis (PROTOCOL_E3_ABLATION Amendment 1: v2 four-variant ablation
# and closed loop) runs by itself from RUN_marl_e3_dense.sh and stays the registered endpoint.  This ADDED analysis
# (with the always-keep-prefix option) uses the SAME v3 trainer everywhere:
#   arms trained on the dense labels (dense/selectors_v3):
#     legal_bid_resp_origsel   dense TRAIN, ORIGINAL select split, 40 epochs   -- the clean data-density comparison
#     legal_bid_resp_matched   dense TRAIN, ORIGINAL select split, 13 epochs   -- matched gradient steps (768 x 40 ~ 2432 x 13)
#     legal_bid_resp           dense TRAIN + dense select, 40 epochs           -- the full registered dense recipe
#     priv_only                dense TRAIN + dense select                      -- diagnostic (never deployable)
#   against the original arms (selectors_v3: legal_bid_resp, priv_only);
#   every arm scored on ONE common label table at a time (the two rounds draw different candidates at the same
#   (episode, t)): (a) the original 48 development states, (b) the full dense development panel (304 states);
#   episode and traffic-seed bootstraps (MARL_e3_paired_eval.py); diagnostic v3 (harm | edit, tie-half pair accuracy, regret);
#   resources: labelled candidates and distinct traffic episodes per training set (f1_resources.json);
#   the registered acquisition v2 ablation on the dense labels (PROTOCOL_E3_DELAY_ACQ B).
# Refuses to start unless every dense label directory is complete and self-check PASS, and the label audit passes.
# Usage: bash scripts/RUN_marl_e3_dense_f1.sh <actor dir>      DRY=1 checks inputs and prints the plan only.
# (28/09 16:5x) also runs the registered v2 ablation first when RUN_marl_e3_dense.sh did not, under an owner lock.
# (28/09 19:2x, handoff 19:10 W1, ledger L-58; this runner had never run past DRY) the selector diagnostic is v3 (tie-half)
# via RUN_marl_e3_diag_v3.sh -> dense/selectors_v3_diag_v3.json, and the acquisition stage is RUN_marl_e3_acq2_dv3.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
A="${1:?actor dir}"; D="$A/dense"
for L in "$D"/labels_train_[0-9]* "$D"/labels_select "$D"/labels_dev; do
  case "$L" in *.log) continue ;; esac
  [ -f "$L/manifest.json" ] || { echo "refusing: $L is not complete"; exit 2; }
  python3 -c "import json,sys; m=json.load(open(sys.argv[1])); assert m['self_check']=='PASS', sys.argv[1]" "$L/manifest.json"
done
python3 scripts/MARL_e3_labels_audit.py "$D/labels_*" --out "$A/f1_dense_labels_audit.json" > "$A/f1_dense_labels_audit.txt" || { echo "refusing: dense label audit found a defect"; cat "$A/f1_dense_labels_audit.txt"; exit 2; }
for f in "$A"/selectors_v3/model_legal_bid_resp_s{0,1,2}.pt "$A"/selectors_v3/model_priv_only_s{0,1,2}.pt; do [ -f "$f" ] || { echo "missing original arm $f"; exit 2; }; done
echo "F1 plan for $A: registered v2 ablation if missing; v3 arms on $D; paired eval on $A/labels_dev and $D/labels_dev; diag v3; resources; acquisition v2 (diag v3) on $D  $(date)"
[ "${DRY:-0}" = 1 ] && { echo "DRY run: inputs OK"; exit 0; }
# one owner per run (28/09 double-writer incident, ledger L-53): an atomic mkdir lock; a second launcher refuses
LOCK="$D/.f1_owner_lock"; mkdir "$LOCK" 2>/dev/null || { echo "refusing: $LOCK exists (another F1 run owns $D: $(cat $LOCK/owner 2>/dev/null))"; exit 4; }
echo "pid $$ host $(hostname) started $(date)" > "$LOCK/owner"
# the REGISTERED analysis (PROTOCOL_E3_ABLATION Amendment 1). RUN_marl_e3_dense.sh no longer starts it, because a dense
# shard exhausted its watchdog retries (ledger L-51). Skipped stage by stage if already complete
bash scripts/RUN_marl_e3_ablation.sh "$D"
python3 - "$A" > "$A/f1_resources.json" <<'EOF'
import gzip, json, sys
from pathlib import Path
A = Path(sys.argv[1]); out = {}
for name, pat in (('original', 'labels_train_*'), ('dense', 'dense/labels_train_*')):
    st = cand = 0; eps = set()
    for d in sorted(A.glob(pat)):
        if not d.is_dir(): continue
        for l in gzip.open(d / 'labels.jsonl.gz', 'rt'):
            r = json.loads(l); st += 1; cand += len(r['cands']); eps.add(r['episode_id'])
    out[name] = dict(train_states=st, labelled_candidates=cand, distinct_traffic_episodes=len(eps))
print(json.dumps(out, indent=1))
EOF
O="$D/selectors_v3"; PIDS=""
for s in 0 1 2; do
  for v in "legal_bid_resp_origsel|--bid --resp|$A/labels_select|40" "legal_bid_resp_matched|--bid --resp|$A/labels_select|13" \
           "legal_bid_resp|--bid --resp|$D/labels_select|40" "priv_only|--priv-joint|$D/labels_select|40"; do
    IFS='|' read -r N FL SEL EP <<< "$v"
    [ -f "$O/job_${N}_s$s.json" ] || { $PY -u scripts/MARL_e3_selector_train_v3.py --train "$D/labels_train_*" --select "$SEL" --dev "$D/labels_dev" \
        --out "$O" --name $N $FL --seed $s --epochs $EP > "$D/v3_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  done
done
for p in $PIDS; do wait $p; done
ARMS=(--arm 'orig_legal=selectors_v3/model_legal_bid_resp_s*.pt' --arm 'dense_legal_origsel=dense/selectors_v3/model_legal_bid_resp_origsel_s*.pt'
      --arm 'dense_legal_matched=dense/selectors_v3/model_legal_bid_resp_matched_s*.pt' --arm 'dense_legal_full=dense/selectors_v3/model_legal_bid_resp_s*.pt'
      --arm 'orig_priv=selectors_v3/model_priv_only_s*.pt' --arm 'dense_priv=dense/selectors_v3/model_priv_only_s*.pt')
$PY -u scripts/MARL_e3_paired_eval.py --actor-dir "$A" "${ARMS[@]}" --out "$A/f1_paired_original_states.json" > "$A/f1_paired_original_states.txt" 2>&1
$PY -u scripts/MARL_e3_paired_eval.py --actor-dir "$A" --labels "$D/labels_dev" "${ARMS[@]}" --out "$A/f1_paired_dense_dev.json" > "$A/f1_paired_dense_dev.txt" 2>&1
bash scripts/RUN_marl_e3_diag_v3.sh "$D" selectors_v3 > /dev/null
echo "== resources"; cat "$A/f1_resources.json"
echo "== F1 on the original 48 development states (one table)"; cat "$A/f1_paired_original_states.txt"
echo "== F1 on the full dense development panel (one table)"; cat "$A/f1_paired_dense_dev.txt"
echo "== diagnostic v3 (tie-half) of the dense v3 arms (dense select/dev)"; cat "$D/selectors_v3_diag_v3.txt"
bash scripts/RUN_marl_e3_acq2_dv3.sh "$D"
echo "F1 done $A $(date)"
