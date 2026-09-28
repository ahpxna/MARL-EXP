#!/usr/bin/env python3
"""B2 confirmation-panel collector (research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md §4).

Runs the B1 collector (scripts/MARL_hetero_lc_collect.py, imported and unchanged) on the FRESH
confirmation seeds 601-616, headways 8 and 16, split name 'confirm'.  Only the episode list and
the dependency list are replaced; environment, actor, snapshots, capacity vectors, candidate
family, checks and manifest are the B1 collector's.  --shard/--nshards/--smoke/--mini as there.
"""
from __future__ import annotations
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_lc_collect as lc

CONFIRM = list(range(601, 617))


def episode_list(smoke):
    seeds = CONFIRM[:1] if smoke else CONFIRM
    return [('confirm', s, load) for s in seeds for load in (lc.LOADS[:1] if smoke else lc.LOADS)]


lc.episode_list = episode_list
lc.DEPENDENCIES = lc.DEPENDENCIES + ['scripts/MARL_hetero_b2_collect.py',
                                     'research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md']

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    p.add_argument('--mini', action='store_true')
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    lc.run(p.parse_args())
