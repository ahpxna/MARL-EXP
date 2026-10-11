#!/usr/bin/env python3
"""Convention-corrected forecast provider (PROTOCOL_CITY_F1 §0; C-71): CITY_spat_forecast.make_spat (unchanged) with ttg + 1 s when the light is
in a GREEN phase and the link is served by the other green (a setPhase-initiated yellow is observed for 4 s).  Everything else is identical."""
import scripts.CITY_env as CE
import scripts.CITY_spat_forecast as FC


def make_spat_c(table, q):
    base, F = FC.make_spat(table, q)

    def spat_c(tid, link):
        s = base(tid, link)
        if s['valid'] and s['ttg'] > 0 and CE.ls.trafficlight.getPhase(tid) in F.G[tid]:
            s = dict(s, ttg=s['ttg'] + 1.0, source=s['source'] + '+c')
        return s
    return spat_c, F
