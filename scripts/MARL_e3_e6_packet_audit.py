#!/usr/bin/env python3
"""E6 trace-level audit (03/10/2026 23:2x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 E6).  For the K1 legacy view that the
receiver-side emulator must rebuild, count the entries whose copy the receiver has (a) seen at all and (b) seen at a reception
age < 14 decision steps — only (b) has a measurement time recoverable from the 25 B packet's 4-bit age field (saturated at 14).
Schedules depend on the exogenous capacity trace only (scripts/MARL_e3_p2_replay_feasibility.py); slot mirror on 4x4.
Channels: U2 (order-preserving) and U1 (deployed iid).  Episodes 301-364 and 901-904 x 8/16 (not a panel)."""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_p2_replay_feasibility import schedule, trace
from scripts.MARL_hetero_pilot_collect import N_DEC
from models.marl_relay_v3 import nearest_slots, make_slot_mirror
from models.marl_hetero_selector import prefix_sets
from models.marl_delivery_music import AgeMirror, NEVER
CAP = 14


def audit(sch_old, sch_new, m, slots):
    Mir = make_slot_mirror(slots) if slots else AgeMirror
    mo, mn = Mir(m), Mir(m); seen = [[dict() for _ in range(m)] for _ in range(m)]; c = dict(entries=0, seen=0, packet=0)
    for t in range(N_DEC):
        S = sch_new[t][1]; prev = mn.table.copy()
        for i in range(m):
            for k in S[i]:
                seen[i][k][t] = 0
                for j in range(m):
                    if j != i and prev[k, j] > NEVER / 2 and (not slots or j in slots[k]):
                        tau = prev[k, j]; seen[i][j][tau] = min(seen[i][j].get(tau, 10 ** 9), int(round(t - tau)))
        mo.update(sch_old[t][1], t); mn.update(S, t)
        for i in range(m):
            for j in range(m):
                ms = mo.table[i, j]
                if j == i or ms <= NEVER / 2:
                    continue
                c['entries'] += 1; a = seen[i][j].get(ms)
                if a is not None:
                    c['seen'] += 1; c['packet'] += a < CAP
    return c


def main():
    res = {}
    for m, sl in ((16, nearest_slots(4, 4)), (9, None)):
        k1 = schedule(lambda t: [1] * m, m, N_DEC); tot = {'U1': dict(entries=0, seen=0, packet=0), 'U2': dict(entries=0, seen=0, packet=0)}
        for s in list(range(301, 365)) + list(range(901, 905)):
            for h in (8, 16):
                tr = trace(s, h, m, N_DEC)
                u1 = schedule(lambda t: tr[t], m, N_DEC)
                u2 = [(k1[t][0], prefix_sets(k1[t][0], [int(k) for k in tr[t]]), None) for t in range(N_DEC)]
                for name, sch in (('U1', u1), ('U2', u2)):
                    c = audit(k1, sch, m, sl)
                    for k in c:
                        tot[name][k] += c[k]
        res[f'{m}_agents'] = {n: dict(v, seen_share=v['seen'] / v['entries'], packet_share=v['packet'] / v['entries'],
                                      ambiguous_share=(v['seen'] - v['packet']) / v['entries']) for n, v in tot.items()}
        print(m, json.dumps(res[f'{m}_agents']), flush=True)
    out = ROOT / 'research/marl_budget/e3_wave_20261003/e6_packet_audit.json'; out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=1)); print('wrote', out)


if __name__ == '__main__':
    main()
