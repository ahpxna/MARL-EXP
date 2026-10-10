#!/usr/bin/env python3
"""Convention-complete provider c2 (PROTOCOL_CITY_F1B_20261004 B0): the OLD-format CITY_spat_forecast table (same duration samples, no refit)
augmented with the net program's non-green durations (CITY_spat_forecast_k.program on Q7.NET_S), served by CITY_spat_forecast_k.make_spat_k,
which is convention-corrected in every branch (C-71 and C-84).  On grid4 it must differ from CITY_spat_forecast_c ONLY in the yellow ->
green-after-next branch, by exactly +1 s (check KB0-3).  CITY_spat_forecast_c, its tables and every F1 / F1-A1 artefact are unchanged."""
import scripts.CITY_q7_cross_version as Q7
import scripts.CITY_spat_forecast_k as FK


def augment(table, net_file=None):
    PR = FK.program(net_file or Q7.NET_S); T = dict(table)
    bad = [t for t in table['greens'] if t not in PR or list(PR[t][0]) != list(table['greens'][t])]
    if bad:
        raise SystemExit(f'c2: greens of {bad[:3]} differ between the table and the net programs')
    T['ng'] = {t: FK.ng_of(*PR[t][:3]) for t in table['greens']}; T['n_phases'] = {t: PR[t][1] for t in table['greens']}
    T['dur'] = {t: PR[t][2] for t in table['greens']}; T['kind'] = 'c2:' + str(table.get('kind', 'forecast')); return T


def make_spat_c2(table, q):
    return FK.make_spat_k(augment(table), q)
