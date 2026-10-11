#!/usr/bin/env python3
"""M3′-D report (PROTOCOL_CITY_M3P_DIAG_20261004; written before the panel).  Dir m3pd_20261004: dev/C<FM>_k<k>_<fl>[_sh] (closed loop, cells
FM in 11 registered / 01 no forced hold / 10 kept message / 00 both), replay/<msg>_k<k>_<fl> (open loop on the recorded C11 schedule).  R rows:
m3_20261004/dev/R_k<k>_<fl>.  Registered RPC rows (KD-1): m3p_20261004/dev/RPC_receiver_k<k>_<fl>.  Cube [k 2, fleet 2, traffic 15], crossed."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'm3pd_20261004'; S = [100, 101, 102, 103, 104] + list(range(200, 210)); K = (0, 1); FL = ('s13', 's113')
Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports')


def cub(Rt, A, B, key='fuel_agent', pct=True, den=None):
    den = den or B
    return np.array([[[100 * (Rt[A(k, f)][s][key] - Rt[B(k, f)][s][key]) / Rt[den(k, f)][s][key] if pct else Rt[A(k, f)][s][key] - Rt[B(k, f)][s][key] for s in S] for f in FL] for k in K])


def ci(c):
    dr = R.draws(c.shape); p, c2, up = R.crossed(c, dr); lo = float(np.percentile([c[np.ix_(*ix)].mean() for ix in dr], 5))
    return f'{p:+.2f} [{c2[0]:+.2f}, {c2[1]:+.2f}] (lo {lo:+.2f}, up {up:+.2f})'


if __name__ == '__main__':
    Rt = {**rows(CS / 'm3_20261004/dev'), **{f'REG_{k}': v for k, v in rows(CS / 'm3p_20261004/dev').items()}, **rows(D / 'dev'), **{f'REP_{k}': v for k, v in rows(D / 'replay').items()}}
    out = ['== M3′-D: RPC 2 x 2 (F forced hold 1/0 x M message withdrawn 1 / kept 0), M3′ DEV panel; vs R (no SPaT)']
    kd1 = all(Rt[f'C11_k{k}_{f}'][s][q] == Rt[f'REG_RPC_receiver_k{k}_{f}'][s][q] for k in K for f in FL for s in S for q in Q)
    out.append(f'  KD-1 (F1, M1) new code == registered RPC rows (all 60 cells): {"PASS" if kd1 else "FAIL"}')
    Rb = lambda k, f: f'R_k{k}_{f}'
    for c, nm in (('11', 'F1 M1 registered'), ('01', 'F0 M1 no forced hold'), ('10', 'F1 M0 kept message'), ('00', 'F0 M0 both')):
        A = lambda k, f, c=c: f'C{c}_k{k}_{f}'; Sh = lambda k, f, c=c: f'C{c}_k{k}_{f}_sh'
        side = [json.loads((D / f'dev/C{c}_k{k}_{f}_m3p.json').read_text())['per_seed'] for k in K for f in FL]; s2 = [json.loads((D / f'dev/C{c}_k{k}_{f}_m3p2.json').read_text())['per_seed'] for k in K for f in FL]
        v = sum(x['viol_end'] + x['viol_onset'] for d in side for x in d.values()); com = sum(x['commits'] for d in side for x in d.values())
        isw = sum(x['issue_switch'] for d in s2 for x in d.values()); ike = sum(x['issue_keep'] for d in s2 for x in d.values())
        hsw = sum(x['held_switch'] for d in s2 for x in d.values()); hke = sum(x['held_keep'] for d in s2 for x in d.values())
        out.append(f'  {nm}: M3-1 agent fuel % {ci(cub(Rt, A, Rb))} | city TL {ci(cub(Rt, A, Rb, "timeloss", False))} | agent TL {ci(cub(Rt, A, Rb, "timeloss_agent", False))} | human TL {ci(cub(Rt, A, Rb, "timeloss_human", False))}')
        out.append(f'      x mechanism cost {ci(cub(Rt, Sh, Rb, den=Rb))} | y fleet contribution {ci(cub(Rt, A, Sh, den=Rb))} | commits {com}, violations {v} | '
                   f'issued against a switch {isw}/{isw + ike} = {isw / max(1, isw + ike):.2f} | held ticks where RL-H would switch {hsw}/{hsw + hke} = {hsw / max(1, hsw + hke):.2f}')
    for a, b, nm in (('01', '11', 'F effect at M1 (F0 - F1)'), ('00', '10', 'F effect at M0'), ('10', '11', 'M effect at F1 (M0 - M1)'), ('00', '01', 'M effect at F0')):
        out.append(f'  {nm}: agent fuel % {ci(cub(Rt, lambda k, f, a=a: f"C{a}_k{k}_{f}", lambda k, f, b=b: f"C{b}_k{k}_{f}", den=Rb))} | agent TL {ci(cub(Rt, lambda k, f, a=a: f"C{a}_k{k}_{f}", lambda k, f, b=b: f"C{b}_k{k}_{f}", "timeloss_agent", False))}')
    if all(f'REP_{m}_k{k}_{f}' in Rt for m in ('withdraw', 'keep') for k in K for f in FL):
        kd3 = all(Rt[f'REP_withdraw_k{k}_{f}'][s][q] == Rt[f'C11_k{k}_{f}'][s][q] for k in K for f in FL for s in S for q in Q)
        out.append(f'  KD-3 replay (withdraw) == closed-loop (F1, M1): {"PASS (bit-identical)" if kd3 else "NOT identical: H2 open-loop step is approximate"}')
        if not kd3:
            out.append(f'      replay(withdraw) - closed-loop fuel % {ci(cub(Rt, lambda k, f: f"REP_withdraw_k{k}_{f}", lambda k, f: f"C11_k{k}_{f}", den=Rb))}')
        out.append(f'  H2 open loop (same light schedule): keep - withdraw agent fuel % {ci(cub(Rt, lambda k, f: f"REP_keep_k{k}_{f}", lambda k, f: f"REP_withdraw_k{k}_{f}", den=Rb))} | agent TL '
                   f'{ci(cub(Rt, lambda k, f: f"REP_keep_k{k}_{f}", lambda k, f: f"REP_withdraw_k{k}_{f}", "timeloss_agent", False))} | human TL {ci(cub(Rt, lambda k, f: f"REP_keep_k{k}_{f}", lambda k, f: f"REP_withdraw_k{k}_{f}", "timeloss_human", False))}')
    t = '\n'.join(out) + '\n'; (D / 'report_m3pd.txt').write_text(t); print(t)
