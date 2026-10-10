#!/usr/bin/env python3
"""Report of E9b / E9c (PROTOCOL_E3_WAVE_ALL_PENDING_20261003, E9b and E9c addenda; written 04/10/2026 00:3x EDT, before
the E9c runs and before the E9b panel was complete).  Endpoints exactly as registered:
  E9b-1 zero mismatches (packets / cache / view / input / action) and zero missing base packets on dev, seeds 0-9;
  E9b-2 E9b panel decoder queue == E7 U2/EXACT_PROTO_OLD queue on every (seed, layout, episode);
  E9c-1 full and wire5: zero mismatches in every part (incl. ts, old_dec) and zero missing on dev; wire5 panel zero
        mismatches and queue == the E9b decoder queue on every episode;
  E9c-2 wire4 mismatch counts per part (exploratory);
  E9c-3 every control has > 0 view mismatches on every dev seed and layout; u2table and empty have > 0 action mismatches
        summed over each seed's dev episodes; relay_needed > 0 on every dev seed.
Costs per episode: base packets delivered / decoded by all agents and unique base broadcasts (x 25 B), bits per base packet.
A part with missing runs is INCOMPLETE (never SUPPORTED)."""
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np

W = Path('research/marl_budget/e3_wave_20261003'); SEEDS = list(range(10)); PKT = 25
DEV_EPS = [f'seed{t}_load{h}' for t in (901, 902, 903, 904) for h in (8, 16)]
PANEL_EPS = [f'seed{t}_load{h}' for t in range(7501, 7565) for h in (8, 16)]


def load(d):
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
    return json.loads((d / 'rows.json').read_text())


def verdict(ok, miss):
    return 'INCOMPLETE' if miss else ('SUPPORTED' if ok else 'NOT SUPPORTED')


def main(a):
    out = []; E9B = W / 'e9b'; E9C = W / a.e9c_dir
    # E9b-1
    miss = []; bad = []
    for s in SEEDS:
        r = load(E9B / f'DEV_s{s}')
        if r is None:
            miss.append(s); continue
        for x in r:
            if sum(x['mismatches'].values()) or x['legacy_missing']:
                bad.append((s, x['layout'], x['episode'], x['mismatches'], x['legacy_missing']))
    out.append(f'E9b-1 dev per-step parity (seeds {SEEDS}): bad episodes {len(bad)} {bad[:3]} missing seeds {miss} -> {verdict(not bad, miss)}')
    # E9b-2
    miss = []; diff = []; n = 0; dq = {}
    for s in SEEDS:
        r = load(E9B / f'PANEL_s{s}')
        if r is None:
            miss.append(('E9b', s)); continue
        for x in r:
            dq[(s, x['layout'], x['episode'])] = x['queue_sum']
        for lay in ('D', 'C'):
            e7 = load(W / 'w2' / f'MIX_s{s}_{lay}')
            if e7 is None:
                miss.append(('E7', s, lay)); continue
            ref = {x['episode']: x['queue_sum'] for x in e7 if x['arm'] == 'U2/EXACT_PROTO_OLD'}
            for ep in PANEL_EPS:
                n += 1
                if abs(dq[(s, lay, ep)] - ref[ep]) > 1e-6:
                    diff.append((s, lay, ep, dq[(s, lay, ep)], ref[ep]))
    out.append(f'E9b-2 panel decoder queue == E7 EXACT_PROTO_OLD: {n - len(diff)}/{n} equal, differences {diff[:3]}; missing {miss[:4]} -> {verdict(not diff, miss)}')
    # E9c-1 / E9c-2 / E9c-3
    miss = []; dev = {}; panel = {}
    for s in SEEDS:
        r = load(E9C / f'DEV_s{s}')
        if r is None:
            miss.append(('DEV', s))
        else:
            dev[s] = r
        r = load(E9C / f'PANEL_s{s}')
        if r is None:
            miss.append(('PANEL', s))
        else:
            panel[s] = r
    bad1 = [(s, x['arm'], x['layout'], x['episode'], {k: v for k, v in x['mismatches'].items() if v}, x['legacy_missing'])
            for s, r in dev.items() for x in r if x['fmt'] in ('full', 'wire5') and not x['corrupt'] and (sum(x['mismatches'].values()) or x['legacy_missing'])]
    bad1 += [(s, x['arm'], x['layout'], x['episode'], {k: v for k, v in x['mismatches'].items() if v}, x['legacy_missing'])
             for s, r in panel.items() for x in r if x['fmt'] == 'wire5' and (sum(x['mismatches'].values()) or x['legacy_missing'])]
    qd = [(s, x['layout'], x['episode']) for s, r in panel.items() for x in r if x['fmt'] == 'wire5'
          if (s, x['layout'], x['episode']) in dq and abs(x['queue_sum'] - dq[(s, x['layout'], x['episode'])]) > 1e-6]
    out.append(f'E9c-1 full / wire5 parity (dev + panel) and wire5 panel queue == E9b: bad {len(bad1)} {bad1[:3]}; queue differences {len(qd)} {qd[:3]}; '
               f'missing {miss[:4]} -> {verdict(not bad1 and not qd, miss)}')
    w4 = defaultdict(int); w4n = 0
    for blk in (dev, panel):
        for s, r in blk.items():
            for x in r:
                if x['fmt'] == 'wire4' and not x['corrupt']:
                    w4n += 1
                    for k, v in x['mismatches'].items():
                        w4[k] += v
    out.append(f'E9c-2 wire4 (exploratory) over {w4n} episodes: mismatches {dict(w4)}' + (' [INCOMPLETE]' if miss else ''))
    ok3 = True; det = []
    for s, r in dev.items():
        rn = sum(x['relay_needed'] for x in r if x['fmt'] == 'full' and not x['corrupt'])
        ok3 &= rn > 0
        for c in ('ages', 'empty', 'u2table', 'stale'):
            rows = [x for x in r if x['corrupt'] == c]
            v = {lay: sum(x['mismatches']['view'] for x in rows if x['layout'] == lay) for lay in ('ALL', 'D', 'C')}
            act = sum(x['mismatches']['action'] for x in rows)
            ok3 &= all(val > 0 for val in v.values()) and (act > 0 if c in ('u2table', 'empty') else True)
            det.append((s, c, v, act))
    out.append(f'E9c-3 controls detected on every dev seed / layout, relay_needed > 0: -> {verdict(ok3, [m for m in miss if m[0] == "DEV"])}')
    for c in ('ages', 'empty', 'u2table', 'stale'):
        dd = [d for d in det if d[1] == c]
        if dd:
            out.append(f'  {c}: view mismatches per seed (min over layouts) {[min(d[2].values()) for d in dd]}, action mismatches per seed {[d[3] for d in dd]}')
    # queue effect of each control vs the clean decoder (diagnostic), mixed layouts
    for lay in ('D', 'C'):
        cl = {(s, x['episode']): x['queue_sum'] for s, r in dev.items() for x in r if x['fmt'] == 'full' and not x['corrupt'] and x['layout'] == lay}
        if not cl:
            continue
        line = []
        for c in ('ages', 'empty', 'u2table', 'stale'):
            q = {(s, x['episode']): x['queue_sum'] for s, r in dev.items() for x in r if x['corrupt'] == c and x['layout'] == lay}
            if q:
                line.append(f"{c} {-(sum(q.values()) / sum(cl[k] for k in q) - 1) * 100:+.2f} %")
        out.append(f'  layout {lay}: system queue gain of each control relative to the clean decoder (dev, pooled): ' + ', '.join(line))
    # costs
    for blk, nm in ((dev, 'dev'), (panel, 'panel')):
        rr = [x for r in blk.values() for x in r if not x['corrupt']]
        if rr:
            out.append(f"Cost ({nm}, per episode): base packets delivered/decoded by all agents {np.mean([x['base_delivered'] for x in rr]):.0f} "
                       f"(= {np.mean([x['base_delivered'] for x in rr]) * PKT:.0f} B), unique base broadcasts {np.mean([x['base_unique'] for x in rr]):.0f} "
                       f"(= {np.mean([x['base_unique'] for x in rr]) * PKT:.0f} B); bits per base packet: wire4 185, wire5 193 (<= 200)")
    txt = '\n'.join(out) + '\n'; (W / a.out).write_text(txt); print(txt)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--e9c-dir', default='e9c'); p.add_argument('--out', default='e9_report.txt')
    main(p.parse_args())
