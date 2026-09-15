"""Check an entire affine margin family using exact endpoint certificates.

For F_t=(1-t)F_0+tF_1, 0<=t<=1, all mixed-difference inequalities are
preserved by convexity. Common residual extrema make the two oscillations
affine. Same-sign responses make their spans affine. Combined with the
margin-sensitive exchange theorem, this proves the indicated frontier on
the interval. This endpoint checker is exact Python, not a Lean bridge.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import hashlib
import json

ROOT = Path('/Users/phanan/cig-amf-main/research/d6_frontier_20260908')


def check(m):
    source = ROOT / f'frontier_m{m}_block.json'
    data = json.loads(source.read_text())
    ends = [next(p for p in data['points'] if p['mu'] == str(t)) for t in (0, 1)]
    k, cube = m // 2, list(product((0, 1), repeat=m))
    selected, competitor = tuple(range(k)), tuple(range(k, m))
    key = lambda x: (x[0], sum(x[1:k]), x[k], sum(x[k+1:]))
    residuals, responses, gaps, derivative_spreads = [], [], [], []
    for t, point in enumerate(ends):
        table = {tuple(r['class']): Q(r['value']) for r in point['world_classes']}
        world = {x: table[key(x)] for x in cube}
        zero = (0,) * m
        response = []
        for j in range(m):
            one = list(zero); one[j] = 1
            response.append(world[tuple(one)] - world[zero])
        assert all(abs(response[j]) == 1 for j in selected)
        assert all(abs(response[j]) == 1-t for j in competitor)
        responses.append(response)
        rr = [{x: world[x]-sum(response[j]*x[j] for j in keep) for x in cube}
              for keep in (selected, competitor)]
        residuals.append(rr)
        gap = max(rr[0].values())-min(rr[0].values())-max(rr[1].values())+min(rr[1].values())
        assert gap == m-k*t
        gaps.append(str(gap))
        spreads = []
        for j in range(m):
            derivative = []
            for x in cube:
                if x[j]:
                    continue
                y = list(x); y[j] = 1
                derivative.append(world[tuple(y)]-world[x])
            spread = max(derivative)-min(derivative)
            assert spread <= 1
            spreads.append(str(spread))
        derivative_spreads.append(spreads)
    assert all(a*b >= 0 for a,b in zip(*responses))
    extrema = []
    for side in (0,1):
        a, b = residuals[0][side], residuals[1][side]
        low = sorted(x for x in cube if a[x] == min(a.values()) and b[x] == min(b.values()))
        high = sorted(x for x in cube if a[x] == max(a.values()) and b[x] == max(b.values()))
        assert low and high, 'No common extrema: interpolation argument unavailable'
        extrema.append({'common_min':low[0], 'common_max':high[0]})
    return {'m':m, 'k':k, 'interval':['0','1'], 'endpoint_gaps':gaps,
            'endpoint_derivative_spreads':derivative_spreads, 'extrema':extrema,
            'response_signs_consistent':True, 'formula':f'{m} - {k} * mu',
            'source':str(source), 'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'status':'EXACT_ENDPOINT_CHECKS_PASS_LOWER_BRIDGE_NOT_YET_LEAN'}


if __name__ == '__main__':
    rows = [check(m) for m in (6,8)]
    Path(__file__).with_suffix('.json').write_text(json.dumps(rows, indent=2))
    for row in rows:
        print(row['m'], row['formula'], 'on [0,1]: exact endpoint checks pass')
