#!/usr/bin/env python3
"""B6-G report (PROTOCOL_CITY_B6 §B6-G, registered 04/10/2026 wake 9 before the run): σ 0.3 and ACC fleet upgrades under frozen RL-C50 / RL-J,
VALIDATION 200-209.  New rows: wave2_20261004/054 (OFF_<L>, S0.3_<L>, acc_<L>); ACT reference rows: 049v (S0.3_ACT, S0.5_ACT) and 053v (acc_ACT, OFF_ACT)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

VAL = list(range(200, 210)); FAM = ('RL-C50', 'RL-J')


def rows(*ds):
    Rt = {}
    for d in ds:
        for f in Path(d).glob('*.json'):
            x = json.loads(f.read_text())
            if isinstance(x, dict) and 'rows' in x:
                for r in x['rows']:
                    Rt[(d.name, f.stem, r['seed'])] = r
    return Rt


def main():
    W = R.W; Rt = rows(W / '054', W / '049v', W / '053v'); dr = R.draws((4, len(VAL))); out = ['== B6-G: fleet upgrades under other frozen learned lights, VALIDATION 200-209']
    act = {'σ0.3': (('049v', 'S0.3_ACT'), ('049v', 'S0.5_ACT')), 'ACC': (('053v', 'acc_ACT'), ('053v', 'OFF_ACT'))}
    up = {'σ0.3': 'S0.3', 'ACC': 'acc'}
    try:
        for fam in FAM:
            for u in ('σ0.3', 'ACC'):
                (da, ta), (db, tb) = act[u]
                c = np.array([[(Rt[('054', f'{up[u]}_{fam}-{i}', s)]['timeloss'] - Rt[('054', f'OFF_{fam}-{i}', s)]['timeloss'])
                               - (Rt[(da, ta, s)]['timeloss'] - Rt[(db, tb, s)]['timeloss']) for s in VAL] for i in range(4)])
                p, ci, upb = R.crossed(c, dr)
                g0 = np.mean([[Rt[('054', f'OFF_{fam}-{i}', s)]['timeloss'] - Rt[('053v', 'OFF_ACT', s)]['timeloss'] for s in VAL] for i in range(4)])
                g1 = np.mean([[Rt[('054', f'{up[u]}_{fam}-{i}', s)]['timeloss'] - Rt[(da, ta, s)]['timeloss'] for s in VAL] for i in range(4)])
                out.append(f'G-1 {fam} x {u}: city-TL interaction {R.fmt(p, ci, upb)} -> {"NO HARM (upper < +0.5)" if upb < 0.5 else "HARM NOT EXCLUDED"}; '
                           f'G-2 light gain {fam} - ACT: SUMO cars {g0:+.2f}, upgraded fleet {g1:+.2f}')
    except KeyError as e:
        out.append(f'B6-G INCOMPLETE (missing {e})')
    txt = '\n'.join(out) + '\n'; (W / 'report_b6g.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main()
