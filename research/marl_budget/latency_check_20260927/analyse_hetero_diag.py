"""Summarise the bounded learner diagnostic (read-only): validation seeds 51-52 only.

For each predictor and cap: repair_R1 and direct realised gain over the unchanged prefix
(mean over the 4 validation episodes, and the per-episode values), harmful-edit and edit rates,
extra bytes; oracle references; MLP seeds shown separately to judge repeatability.
"""
import json, sys
from collections import defaultdict
import numpy as np

rep = json.load(open(sys.argv[1]))
R = rep['results']
caps = ['+0', '+28', '+56', 'none']
first = next(iter(R.values()))
print('oracle references (true argmax among labelled candidates, prefix kept when no gain):')
for cap in caps:
    o1 = first[cap]['oracle_R1']['gain']; oa = first[cap]['oracle_all']['gain']
    print(f'  cap {cap:5s} oracle_R1 {np.mean(list(o1.values())):+6.2f}   oracle_all {np.mean(list(oa.values())):+6.2f}')
print()
for name, res in R.items():
    line = [f'{name:26s}']
    for cap in caps:
        r1 = res[cap]['repair_R1']; d = res[cap]['direct']
        g = list(r1['gain'].values()); gd = list(d['gain'].values())
        line.append(f'{cap}: R1 {np.mean(g):+5.2f} (ep+ {sum(x > 1e-9 for x in g)}/4, harm {np.mean(list(r1["harm"].values())):.2f}, '
                    f'edit {np.mean(list(r1["edit"].values())):.2f}, {np.mean(list(r1["bytes"].values())):+.0f}B) '
                    f'dir {np.mean(gd):+5.2f}')
    print(line[0]); [print('   ', l) for l in line[1:]]
