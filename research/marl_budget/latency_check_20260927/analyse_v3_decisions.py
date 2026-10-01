"""Audit §7 follow-up: per-decision disagreement, paired per-episode differences, worst-k regret.
Reads models_v3/decisions.jsonl.gz (read-only)."""
import gzip, json, sys
from collections import defaultdict
import numpy as np
recs = [json.loads(l) for l in gzip.open(sys.argv[1], 'rt')]
key = lambda r: (r['feature_set'], r['regime'], r['eval'], r['split'])
by = defaultdict(lambda: defaultdict(dict))
for r in recs:
    by[key(r)][(r['seed'], r['episode_id'], r['t'], r['k'])][r['method']] = (r['selected_mask'], r['regret'])
pairs = [('critic_chain_sum', 'critic_per_budget_table'), ('critic_chain_minimax', 'critic_per_budget_table'),
         ('critic_chain_sum_R1', 'critic_chain_sum'), ('direct_budget_network', 'critic_per_budget_table'),
         ('direct_budget_network', 'cached_queue_prefix')]
for kk in sorted(by):
    if kk[3] != 'test' and kk[2] != 'heldout_k_357':
        continue
    d = by[kk]; line = [f'{"/".join(kk)}:']
    for a, b in pairs:
        dis = np.mean([v[a][0] != v[b][0] for v in d.values() if a in v and b in v])
        ep = defaultdict(list)
        for (s, e, t, k), v in d.items():
            if a in v and b in v:
                ep[(s, e)].append(v[a][1] - v[b][1])
        diffs = [np.mean(x) for x in ep.values()]
        line.append(f'  {a} - {b}: disagree {dis:.2f}; paired mean {np.mean(diffs):+.2f} '
                    f'[{np.min(diffs):+.2f},{np.max(diffs):+.2f}] over {len(diffs)} seed-episodes')
    worst = defaultdict(list)
    ctx = defaultdict(lambda: defaultdict(list))
    for (s, e, t, k), v in d.items():
        for m_, (_, reg) in v.items():
            ctx[m_][(s, e, t)].append(reg)
    line.append('  worst-k regret (mean over contexts of max over k): ' + ', '.join(
        f'{m_} {np.mean([max(x) for x in c.values()]):.1f}' for m_, c in sorted(ctx.items())))
    print('\n'.join(line))
