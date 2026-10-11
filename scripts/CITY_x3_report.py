#!/usr/bin/env python3
"""X3 information-value ladder on R's fixed (replayed) light schedule (PROTOCOL_CITY_N2M_MECHANISM_20261005, Amendment X3; written before the
run): sigma* (RPsig), c2 q0.1 (RPc2), N2 q0.5 (RPn2), exact future (RPex, the C-61 oracle, not deployable).  Decision: EXACT ALSO COSTS
AGENT TIME iff RPex - RPsig agent TL lower bound > +0.5 (then the time cost is the frozen fleet's own trade-off, not a forecast error)."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2m_report as M  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n2m_20261005'
if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(CS / 'n2_20261005/dev'), **rows(D / 'dev')}; nm = lambda p: (lambda k, f: f'{p}_k{k}_{f}'); out = ['== X3 information ladder on the replayed R schedule (open loop)']; res = {}
    for a, b in (('RPex', 'RPsig'), ('RPn2', 'RPsig'), ('RPc2', 'RPsig'), ('RPn2', 'RPex'), ('RPex', 'R')):
        res[(a, b)] = M.full(Rt, nm(a), nm(b)); out.append(M.line(f'{a} - {b}', res[(a, b)]))
    lo = res[('RPex', 'RPsig')]['timeloss_agent'][1][0]
    out.append(f'  X3 VERDICT: {"EXACT ALSO COSTS AGENT TIME (fleet trade-off)" if lo > 0.5 else "INFO-LIMITED (exact info does not cost > 0.5 s/veh)"} (lower {lo:+.2f})')
    t = '\n'.join(out) + '\n'; (D / 'report_x3.txt').write_text(t); print(t)
