"""Small, exact analysis helpers for the screening tables; no learned-MARL claims."""
from contextlib import contextmanager
from itertools import combinations
import math

from models.marl_revision_selector import reachable_sets


@contextmanager
def no_oracle_access(env):
    before = dict(env.access_log)
    yield
    if env.access_log != before:
        raise AssertionError(f'oracle access during live selection/action: {before} -> {env.access_log}')


def mask_of(items):
    return sum(1 << i for i in items)


def layer_masks(m, k):
    return [mask_of(c) for c in combinations(range(m), k)]


def headroom(values, ranking):
    m = len(ranking)
    if len(values) != 1 << m or any(not math.isfinite(x) for x in values):
        raise ValueError('need a complete finite value table')
    rows = []
    for k in range(1, m):
        P = mask_of(ranking[:k])
        best = max(values[s] for s in layer_masks(m, k))
        reached = [max(values[mask_of(s)] for s in reachable_sets(ranking, k, R)) for R in (0, 1, 2)]
        if reached != sorted(reached) or any(v > best+1e-9 for v in reached):
            raise AssertionError('incorrect candidate family')
        rows.append(dict(k=k, prefix_mask=P, prefix_value=values[P], oracle_value=best,
                         best_reachable= reached, regret=[best-v for v in reached],
                         repair_gain=[v-values[P] for v in reached]))
    return rows


def episode_means(records, value):
    groups = {}
    for record in records:
        groups.setdefault(record['episode_id'], []).append(float(value(record)))
    return {key: sum(vals)/len(vals) for key, vals in groups.items()}
