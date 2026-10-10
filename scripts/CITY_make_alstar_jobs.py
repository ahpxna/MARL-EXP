#!/usr/bin/env python3
"""Writes the A-L* spool job if and only if B6-2 confirmed a beneficial recipe (PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004.md, decision
tree Branch P, registered 05:47 before any B6 row).  Prepared 04/10/2026 05:5x (wake 4).  A recipe is F* iff its B6-2 verdicts are PASS
on BOTH new policy seeds (t2, t3) on fresh traffic 400-409.  The job evaluates, on SELECT 100-104:
  lights ACT, RL-H_0..3, RL-C50_0..3  x  F* policy seeds t0..t3  x  guards none / fallback / clip / green+oos,
  plus always-SUMO (guard `always`) under every light (the comparator of AL*-2 / AL*-3).
VALIDATION (200-209) for the guard chosen on SELECT is written by the report as a follow-up job, not here.  Exit 0 and no job if no F*."""
import json, sys
from pathlib import Path

W = Path('research/city_sim/wave2_20261004'); P = Path('research/queue_spool_20261004/pending')


def main():
    f = W / '037' / 'b6_verdicts.json'
    if not f.exists():
        print('no B6-2 verdicts: nothing written'); return 0
    v = json.loads(f.read_text()); rec = {}
    for k, ok in v.items():
        r, t = k.rsplit('_t', 1); rec.setdefault(r, {})[t] = ok
    star = sorted(r for r, d in rec.items() if d.get('2') and d.get('3'))
    if not star:
        print(f'B6-2: no recipe passed on both new seeds {rec}: Branch N'); return 0
    R = star[0]; name = R[2:] if R.startswith('U-') else R                 # e.g. L-ACT-v3
    lights = ['ACT'] + [f'RL-H:{t}' for t in range(4)] + [f'RL-C50:{t}' for t in range(4)]
    lines = []
    for L in lights:
        for t in range(4):
            for g in ('none', 'fallback', 'clip', 'green+oos'):
                lines.append(f"--light {L} --fleet U:{name}_t{t} --guard {g} --seeds 100 101 102 103 104 --tag {name}_t{t}_{L.replace(':', '-')}_{g.replace('+', 'P')}")
        lines.append(f"--light {L} --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_{L.replace(':', '-')}")
    job = P / '038_ALstar_select.sh'
    job.write_text(f"# 038 A-L* on the beneficial recipe {name} (B6 decision tree Branch P), SELECT; written by CITY_make_alstar_jobs.py\n"
                   f"cd /Users/phanan/cig-amf-main\n{{ cat <<'CFG'\n" + '\n'.join(lines) + "\nCFG\n} | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/038\n")
    print(f'F* = {name}; wrote {job} ({len(lines)} configs)'); return 0


if __name__ == '__main__':
    sys.exit(main())
