#!/usr/bin/env python3
"""M1 fleet-benefit table (04/10/2026; DESCRIPTIVE summary of the registered R9 confirmation, C-54).  Fresh traffic 450-469, FT.
Rows: each fleet vs always-SUMO, and the learned fleet (GLOSA-LD∘σ*, pooled search seeds 2-5) vs every comparator.  Registered rows come
from lane_d/eval_450 (frozen evaluation); plain GLOSA and GLOSA∘σ* come from lane_d/eval_450_desc (run after the confirmation, descriptive
only, same producers).  Crossed bootstrap, 2000 draws, one-sided 95 % upper bounds."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/lane_d'; S = list(range(450, 470))


def cell(x, k):
    p, ci, up = x[k][0], x[k][1], x[k][2]
    return f'{p:+.2f} [{ci[0]:+.2f}, {ci[1]:+.2f}]'


if __name__ == '__main__':
    Rt = {**rows(D / 'eval_450'), **rows(D / 'eval_450_desc')}; L = [Rt[f'ESLD_s{s}'] for s in (2, 3, 4, 5)]
    names = [('σ* = 0.3 (SUMO driver)', 'S0.3_FT'), ('GLOSA (heuristic, σ 0.5 base)', 'GLOSA_FT'), ('GLOSA∘σ* (no lane release)', 'GLOSAS'),
             ('GLOSA-L∘σ* (rule, R8)', 'GLOSALS')]
    tel = lambda F: np.mean([f[s]['teleports'] for f in F for s in S])
    out = ['== M1 table: fresh traffic 450-469 (20 seeds), FT, agents 50 %; differences vs the comparator (point [95 % CI]); fuel in %, TL in s/veh',
           f'{"fleet":34s} {"vs":24s} {"agent fuel %":24s} {"agent TL":24s} {"human TL":24s} teleports/run']
    for nm, k in names + [('GLOSA-LD∘σ* (learned, 4 x 20)', None)]:
        F = L if k is None else [Rt[k]]; x = cmp(F, Rt['OFF_FT'], S, R.draws((len(F), len(S))))
        out.append(f'{nm:34s} {"always-SUMO":24s} {cell(x, "fuel"):24s} {cell(x, "tl"):24s} {cell(x, "hu"):24s} {tel(F):.2f}')
    for nm, k in names:
        x = cmp(L, Rt[k], S, R.draws((4, len(S))))
        out.append(f'{"GLOSA-LD∘σ* (learned, 4 x 20)":34s} {nm:24.24s} {cell(x, "fuel"):24s} {cell(x, "tl"):24s} {cell(x, "hu"):24s} {tel(L):.2f} vs {tel([Rt[k]]):.2f}')
    out.append(f'always-SUMO teleports/run {tel([Rt["OFF_FT"]]):.2f}; unfinished (all rows) {sum(r[s]["unfinished"] for r in [Rt[k] for k in Rt if k in ("OFF_FT", "S0.3_FT", "GLOSA_FT", "GLOSAS", "GLOSALS")] + L for s in S)}')
    txt = '\n'.join(out) + '\n'; (D / 'M1_table.txt').write_text(txt); print(txt)
