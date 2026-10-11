#!/usr/bin/env python3
"""Horizon trace check for trainer v7 (PROTOCOL_CITY_B6 §B6-H; 04/10/2026 wake 8).  One 300-s episode per mode, same seed, random
policy with a fixed rng (both modes see the same actions until the first divergence of the transition stream is impossible: the
horizon changes only bookkeeping, never a command).  Checks, each of which can fail:
  H-1 the physical run is identical in both modes (same transition count, same multiset of (action, cost)): bookkeeping only;
  H-2 approach mode: every transition whose next state is a NEW approach (distance jumps up by > 0.3 ZONE) does not exist; crossings are terminal;
  H-3 trip mode: chained = (approach-mode terminals) - (trip-mode terminals); every crossing transition has done = 0 and a next state
      with distance jump > 0.3 ZONE; costs equal the approach-mode costs of the same decisions.
Exit code 1 on any failure."""
import os, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_env import run_episode  # noqa: E402
import scripts.CITY_fleet_train_v7 as V7  # noqa: E402


def one(h):
    rng = np.random.default_rng(5)
    pol = lambda O: rng.integers(0, 7, len(O))
    c = V7.CarRLv7(pol, Q7.RHO, 100, 'release', 'cotv', h, record=True); run_episode(Q7.NET_S, Q7.ROU.format(100), 100, None, c, end=300)
    return c


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    A, T = one('approach'), one('trip'); bad = []
    ta, tt = A.trans, T.trans
    key = lambda tr: sorted((int(x[1]), round(float(x[2]), 9)) for x in tr)       # the two modes append in a different ORDER (terminal at scan
    if len(ta) != len(tt) or key(ta) != key(tt):                                     # time vs chained at decision time): compare multisets
        bad.append('H-1 physical/bookkeeping streams differ')
    cross_a = [x for x in ta if x[3][0] - x[0][0] > 0.3]
    if cross_a:
        bad.append(f'H-2 approach mode has {len(cross_a)} crossing transitions')
    na, nt = int(sum(x[4] for x in ta)), int(sum(x[4] for x in tt)); cross_t = [x for x in tt if x[3][0] - x[0][0] > 0.3]
    if T.chained != na - nt or any(x[4] != 0.0 for x in cross_t) or len(cross_t) != T.chained:
        bad.append(f'H-3 chained {T.chained} vs terminals {na}-{nt}={na - nt}; crossing transitions {len(cross_t)}')
    print(f'transitions {len(ta)} / {len(tt)}; terminals approach {na}, trip {nt}; chained {T.chained}; crossing transitions trip {len(cross_t)} (done=0 all: {all(x[4] == 0 for x in cross_t)})')
    print('HORIZON CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
