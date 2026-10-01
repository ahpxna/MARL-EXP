#!/usr/bin/env python3
"""Can the scheduler EMULATE the frozen actor's response from legal data?  (read-only probe; no rollouts, no training)

The protocol lists "the known actor code" as legal scheduler information, and the only input that has ever raised the
selected gain is the actor's ACTUAL joint action (privileged diagnostic, F2-A).  Learned response heads recovered it
poorly (the multi-class head: 44-48% on changed actions, F2-B).  This probe runs the ACTOR NETWORK ITSELF on a view the
scheduler reconstructs, for every candidate profile of every stored development state, and compares the emulated
greedy action with the stored true joint action ('joint' in the labels).
Reconstruction of receiver i's actor input (CommAdapter.encode layout), from legal data only:
  own lanes      z_i (i's last paid payload): per-approach sums split equally over the approach's 3 lanes;
  own phase      z_i phase / elapsed (one decision stale);
  t, agent id    known;
  sender j in S_i  fresh=1, heard=1, age 0, content = z_j (the latest paid copy; one decision stale);
  sender j not in S_i but cached   the receiver MIRROR block (exact: what i holds, its age);
  never heard    the missing encoding.
Reported per actor: accuracy on all (candidate, receiver) pairs; on pairs whose TRUE action differs from the true prefix
action; change detection (emulated change vs true change: precision, recall); and the reconstruction baseline
(emulated prefix action vs true prefix action).
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_comm_actor import CommAdapter, ActorNet, N_PH, SCALE_Q, SCALE_P, SCALE_T
from scripts.MARL_e3_selector_train import load
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_hetero_pilot_collect import N_DEC


def block(zv):
    """12 floats of a scheduler/mirror block -> (present, age_s, phase, elapsed_s, vehicles[4], waiting[4]) in raw units."""
    return zv[0] > 0, zv[1] * 100.0, int(round(zv[2] * 10)), zv[3] * 100.0, np.asarray(zv[4:8]) * 100.0, np.asarray(zv[8:12]) * 100.0


def encode(ad, st, i, S_i):
    m = st['m']; z = np.asarray(st['z']); mir = np.asarray(st['mirror'])
    zi = block(z[1 + 12 * i:1 + 12 * (i + 1)])
    lv = np.repeat(zi[4] / 3.0, 3); lw = np.repeat(zi[5] / 3.0, 3)
    own = np.concatenate([lv / SCALE_Q, lw / SCALE_Q, np.eye(N_PH, dtype=np.float32)[zi[2] if zi[0] else 0],
                          [zi[3] / SCALE_T, st['t'] / N_DEC]])
    blocks = []
    for j in range(m):
        if j == i:
            continue
        b = np.zeros(ad.blk_dim, np.float32); b[-8:] = ad.static[(i, j)]
        k = i * (m - 1) + (j if j < i else j - 1); mb = block(mir[12 * k:12 * (k + 1)]); zj = block(z[1 + 12 * j:1 + 12 * (j + 1)])
        src = None
        if j in S_i and zj[0]:
            src = (1.0, 0.0, zj)
        elif mb[0]:
            src = (0.0, mb[1], mb)
        if src is not None:
            fr, age, p = src
            b[0] = fr; b[1] = 1.0; b[2] = age / SCALE_T; b[3 + p[2]] = 1.0; b[3 + N_PH] = p[3] / SCALE_T
            b[4 + N_PH:8 + N_PH] = p[4] / SCALE_P; b[8 + N_PH:12 + N_PH] = p[5] / SCALE_P
        blocks.append(b)
    return np.concatenate([own, np.eye(m, dtype=np.float32)[i]] + blocks).astype(np.float32)


def main(a):
    rep = {}
    for name, d in a.actor:
        D = Path(d); S, ckp = load([D / 'labels_dev']); ck = torch.load(ckp.pop(), weights_only=False)
        sc = Scenarios(Path(a.scratch) / name); env0, topo0, _, _ = sc.env(501, 8.0)
        ad = CommAdapter(topo0, N_DEC, env0.action_interval)
        if ad.schema() != ck['schema']:
            raise SystemExit('adapter schema differs')
        net = ActorNet(ad.dim, ck['config']['hidden']); net.load_state_dict(ck['actor']); net.eval(); mask = torch.as_tensor(ad.valid_mask())
        tot = cor = chg_tot = chg_cor = tp = fp = fn = 0; p_cor = p_tot = 0
        for st in S:
            m = st['m']; C = st['cands']
            X = np.stack([encode(ad, st, i, set(c['sets'][i])) for c in C for i in range(m)])
            with torch.no_grad():
                A = net(torch.as_tensor(X), mask.repeat(len(C), 1)).argmax(-1).numpy().reshape(len(C), m)
            J = np.array([c['joint'] for c in C]); P_true = J[0]; P_emul = A[0]
            p_cor += int((P_emul == P_true).sum()); p_tot += m
            cor += int((A == J).sum()); tot += A.size
            ch_true = J != P_true[None]; ch_emul = A != P_emul[None]
            chg_tot += int(ch_true[1:].sum()); chg_cor += int(((A == J) & ch_true)[1:].sum())
            tp += int((ch_true & ch_emul)[1:].sum()); fp += int((~ch_true & ch_emul)[1:].sum()); fn += int((ch_true & ~ch_emul)[1:].sum())
        r = dict(states=len(S), prefix_action_accuracy=round(p_cor / p_tot, 4), all_pairs_accuracy=round(cor / tot, 4),
                 changed_pairs_accuracy=round(chg_cor / max(chg_tot, 1), 4), true_change_rate=round(chg_tot / max(tot - p_tot, 1), 4),
                 change_precision=round(tp / max(tp + fp, 1), 4), change_recall=round(tp / max(tp + fn, 1), 4))
        rep[name] = r
        print(f'{name}: prefix-action acc {r["prefix_action_accuracy"]} | all pairs {r["all_pairs_accuracy"]} | CHANGED pairs {r["changed_pairs_accuracy"]} '
              f'(true change rate {r["true_change_rate"]}) | change precision {r["change_precision"]} recall {r["change_recall"]}', flush=True)
    Path(a.out).write_text(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor', nargs=2, action='append', metavar=('NAME', 'DIR'), required=True)
    p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
