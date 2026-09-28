#!/usr/bin/env python3
"""Apply the B2 design-freeze rule MECHANICALLY (PROTOCOL_B2_FRESH_BID_20260927.md §5 + Amendment 1).

Reads the development job files (seed-averaged development gains on 501-508), and for every
candidate (bid in the amended set, policy, C in {+28,+56,+84}) computes
    diff = gain(bid) - max(gain(ctrl_public), gain(ctrl_history))   at the same (C, policy).
Chooses the maximum.  If it is not positive: STOP (writes stop.json, appends a STOP note).
Otherwise writes freeze.json and dev_map.json and appends '## §5 FROZEN DESIGN' to the protocol.
Refuses if the protocol already has a frozen design.
"""
from __future__ import annotations
import argparse, glob, json, time
from pathlib import Path
import numpy as np

PROTO = Path('research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md')
CANDS = ['bid_prefgap', 'bid_flag', 'bid_queue', 'mlp_bid_request', 'mlp_top2', 'mlp_top2_joint']
CTRLS = ['ctrl_public', 'ctrl_history']


def gains(dirs):
    G, where = {}, {}
    for d in dirs:
        for f in glob.glob(f'{d}/job_*.json'):
            j = json.load(open(f)); L = j['learner']
            if L not in CANDS + CTRLS:
                continue
            where[L] = d
            for cap, row in j['results'][L].items():
                for pol in ('repair_R1', 'direct'):
                    G.setdefault((L, cap, pol), []).append(float(np.mean(row[pol]['gains'])))
    return G, where


def main(a):
    text = PROTO.read_text()
    if '## §5 FROZEN DESIGN' in text:
        raise SystemExit('design already frozen')
    if '## Amendment 1' not in text:
        raise SystemExit('Amendment 1 missing')
    G, where = gains(a.dirs)
    for L in CANDS + CTRLS:
        if L not in where:
            raise SystemExit(f'missing development results for {L}')
        if len(G[(L, '+28', 'repair_R1')]) != 3:
            raise SystemExit(f'{L}: expected 3 seeds, found {len(G[(L, "+28", "repair_R1")])}')
    table = []
    for L in CANDS:
        for cap in ('+28', '+56', '+84'):
            for pol in ('repair_R1', 'direct'):
                ctrl = max(CTRLS, key=lambda c: np.mean(G[(c, cap, pol)]))
                diff = np.mean(G[(L, cap, pol)]) - np.mean(G[(ctrl, cap, pol)])
                table.append(dict(bid=L, cap=int(cap[1:]), policy=pol, control=ctrl, diff=float(diff),
                                  bid_gain=float(np.mean(G[(L, cap, pol)])), control_gain=float(np.mean(G[(ctrl, cap, pol)]))))
    table.sort(key=lambda r: -r['diff'])
    best = table[0]
    stamp = time.strftime('%Y-%m-%d %H:%M:%S')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    (out / 'freeze_table.json').write_text(json.dumps(table, indent=1))
    if best['diff'] <= 0:
        (out / 'stop.json').write_text(json.dumps(dict(stop=True, best=best), indent=1))
        PROTO.write_text(text + f"\n## §5 FROZEN DESIGN — STOP ({stamp})\n\nNo candidate has a positive development "
                         f"difference (best {best}). B2 stops; no confirmation data are collected.\n")
        print('STOP', best); return
    freeze = dict(bid=best['bid'], policy=best['policy'], cap=best['cap'], control=best['control'])
    (out / 'freeze.json').write_text(json.dumps(freeze, indent=1))
    devmap = {L: where[L] for L in set([best['bid'], best['control'], 'bid_queue'] + CTRLS)}
    (out / 'dev_map.json').write_text(json.dumps(devmap, indent=1))
    top = '\n'.join(f"| {r['bid']} | +{r['cap']} | {r['policy']} | {r['control']} | {r['bid_gain']:+.3f} | "
                    f"{r['control_gain']:+.3f} | {r['diff']:+.3f} |" for r in table[:8])
    PROTO.write_text(text + f"""
## §5 FROZEN DESIGN ({stamp}; applied mechanically by scripts/MARL_hetero_b2_freeze.py)

Chosen: **bid = {freeze['bid']}, policy = {freeze['policy']}, total cap C = +{freeze['cap']}, control = {freeze['control']}**.
Development difference {best['diff']:+.3f} ({best['bid_gain']:+.3f} vs {best['control_gain']:+.3f}), seed-averaged, 501-508.
Files: `{out}/freeze.json`, `{out}/dev_map.json`, full ranking `{out}/freeze_table.json`. Top 8:

| bid | C | policy | control | bid gain | control gain | diff |
|---|---|---|---|---|---|---|
{top}

No confirmation label existed when this section was written.
""")
    print('FROZEN', freeze)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('dirs', nargs='+'); p.add_argument('--out', required=True)
    main(p.parse_args())
