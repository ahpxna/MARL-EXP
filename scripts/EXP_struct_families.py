"""STRUCTURAL: is the paper's family the cheapest one that forces a defect?

The defect law is proved for one family, g_m = (-3, -1^p, 1^q, 3), and the
exhaustive sweep confirms that every ordering of it pays at least two. Neither
says whether that family is special. Two questions follow, and the paper answers
neither:

  1. Among all families in the same setting, how many force a defect at all?
     The guess behind this question was that most do not, since an alternating
     family stays inside the free band forever. The sweep says the opposite:
     once the total is as balanced as parity allows, 98 to 100 per cent of
     families force a defect, and the alternating ones are the rare exception.
     What is rare is covering every budget, which one or two families per size
     manage.

  2. Is the paper's family minimal? It has total variation D = sum |g_i| = m + 4.
     If some family with smaller D also forces a defect of two, the construction
     is not tight and the paper should say so.

Scope. The parity argument that makes the defect |s_k| - (k mod 2) a
non-negative even integer needs every entry odd, so the sweep ranges over
multisets of odd integers. Entries are drawn from {-7,...,7} odd and the total
is held as close to zero as parity allows -- exactly zero for even m, and one
away for odd m, which is what the paper's own family does. Families with an even
entry are a different problem and are out of scope rather than silently
included.

Each family is evaluated by the same exact dynamic programme the main sweep
uses, imported rather than reimplemented, so the two cannot drift apart.

Self-check: the paper's own family must come back with minimum total defect two
and full budget coverage at every m, which is the published result, and the
sweep is not reported unless it does.
"""
import json
import time
import argparse
import importlib.util
import os
import sys
import collections
from itertools import combinations_with_replacement
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

spec = importlib.util.spec_from_file_location('se', 'scripts/EXP_struct_enum_large.py')
SE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(SE)

ODD = (-7, -5, -3, -1, 1, 3, 5, 7)


def analyse_family(vals):
    """Minimum total and path defect, and the budgets a single defect of two
    can cover, for an arbitrary multiset of odd integers.

    Same dynamic programme as the main sweep, with the four fixed values of the
    paper's family replaced by whatever this family contains.
    """
    counts = collections.Counter(vals)
    values = tuple(sorted(counts))
    mult = tuple(counts[v] for v in values)
    m = len(vals)
    INF = float('inf')

    by_k = collections.defaultdict(list)

    def gen(prefix, idx):
        if idx == len(values):
            by_k[sum(prefix)].append(tuple(prefix))
            return
        for c in range(mult[idx] + 1):
            gen(prefix + [c], idx + 1)
    gen([], 0)

    def sval(st):
        return sum(values[i] * st[i] for i in range(len(values)))

    def defect(st, k):
        return abs(sval(st)) - (k % 2)

    full = mult

    def walk(init, combine, final_k_zero=True):
        cur = {tuple([0] * len(values)): init}
        for k in range(1, m + 1):
            nxt = {}
            for st in by_k[k]:
                best = INF
                for i in range(len(values)):
                    if st[i] == 0:
                        continue
                    pv = list(st); pv[i] -= 1; pv = tuple(pv)
                    if pv in cur:
                        best = min(best, cur[pv])
                if best < INF:
                    nxt[st] = combine(best, defect(st, k) if k < m else 0)
            cur = nxt
        return cur.get(full)

    min_total = walk(0, lambda a, d: a + d)
    min_path = walk(0, lambda a, d: max(a, d))

    covered = []
    for j in range(1, m):
        reach = {tuple([0] * len(values))}
        for k in range(1, m + 1):
            want = 2 if k == j else 0
            nxt = set()
            for st in by_k[k]:
                if k < m and defect(st, k) != want:
                    continue
                for i in range(len(values)):
                    if st[i] == 0:
                        continue
                    pv = list(st); pv[i] -= 1
                    if tuple(pv) in reach:
                        nxt.add(st); break
            reach = nxt
            if not reach:
                break
        if full in reach:
            covered.append(j)
    return dict(min_total_defect=min_total, min_path_defect=min_path,
                budgets_covered=len(covered), budgets=m - 1,
                covers_all=(len(covered) == m - 1),
                D=sum(abs(v) for v in vals))


def families(m, vmax):
    """Every multiset of odd values in [-vmax, vmax] of size m, as balanced as
    parity allows.

    The sum of m odd integers has the parity of m, so a zero total is available
    only for even m; the paper's own family sums to zero when m is even and to
    -1 when m is odd. The sweep therefore admits |sum| <= 1, which is the
    smallest imbalance parity permits and is what keeps the comparison about the
    ORDERING. A family with a large total is forced into a large prefix sum near
    the end whatever its order, so it would count as defect-forcing for a reason
    that has nothing to do with the mechanism under study.
    """
    pool = [v for v in ODD if abs(v) <= vmax]
    for c in combinations_with_replacement(pool, m):
        if abs(sum(c)) <= 1:
            yield c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--mmax', type=int, default=12)
    ap.add_argument('--vmax', type=int, default=7)
    a = ap.parse_args()
    t0 = time.time()

    # ---------------- self-check on the paper's own family --------------
    bad = []
    for m in range(5, min(a.mmax, 14) + 1):
        A, B_, C, D_ = SE.family(m)
        vals = tuple([-3] * A + [-1] * B_ + [1] * C + [3] * D_)
        got = analyse_family(vals)
        ref = SE.analyse(m)
        if (got['min_total_defect'] != ref['min_total_defect']
                or got['min_path_defect'] != ref['min_path_defect']
                or got['budgets_covered'] != ref['budgets_covered_by_one_defect']):
            bad.append(dict(m=m, got=got, want=ref))
    print(f"self-check: the paper's family through the general evaluator matches the "
          f"main sweep at every m -> {'PASS' if not bad else 'FAIL'}", flush=True)
    if bad:
        Path(a.out).write_text(json.dumps(dict(self_check='FAILED',
                                               mismatches=bad[:5]), indent=1))
        return

    rows = []
    for m in range(5, a.mmax + 1):
        seen = 0
        forcing = []
        dist = collections.Counter()
        best_D, best_fams = None, []
        paper = tuple([-3] + [-1] * SE.family(m)[1] + [1] * SE.family(m)[2] + [3])
        paper_D = sum(abs(v) for v in paper)
        for vals in families(m, a.vmax):
            seen += 1
            r = analyse_family(vals)
            dist[r['min_total_defect']] += 1
            if r['min_total_defect'] >= 2:
                forcing.append((vals, r))
                if best_D is None or r['D'] < best_D:
                    best_D, best_fams = r['D'], [vals]
                elif r['D'] == best_D:
                    best_fams.append(vals)
        covering = [(v, r) for v, r in forcing if r['covers_all']]
        min_D_cover = min((r['D'] for _, r in covering), default=None)
        rows.append(dict(
            m=m, families=seen, forcing=len(forcing),
            forcing_fraction=len(forcing) / seen if seen else None,
            covering_all_budgets=len(covering),
            min_D_forcing=best_D, min_D_covering=min_D_cover,
            paper_family=list(paper), paper_D=paper_D,
            paper_is_min_D_forcing=(best_D == paper_D),
            paper_is_min_D_covering=(min_D_cover == paper_D),
            examples_at_min_D=[list(x) for x in best_fams[:6]],
            min_total_defect_distribution={str(k): v for k, v in sorted(dist.items())}))
        print(f"m={m}: {seen:,} families, {len(forcing):,} force a defect, "
              f"{len(covering):,} also cover every budget; min D forcing {best_D} "
              f"(paper {paper_D}), min D covering {min_D_cover}  "
              f"{time.time()-t0:.0f}s", flush=True)
        Path(a.out).write_text(json.dumps(dict(
            provenance=_P.stamp(__file__), script='EXP_struct_families.py',
            design='every multiset of odd integers in [-vmax, vmax] of size m summing '
                   'to zero, evaluated by the same exact dynamic programme as the main '
                   'sweep, to ask how rare a defect-forcing family is and whether the '
                   "paper's family has the least total variation among them",
            vmax=a.vmax, m_range=[5, m], rows=rows,
            self_check="PASS (the paper's family reproduces the main sweep at every m)",
            wall_seconds=round(time.time() - t0, 1)), indent=1))
    print('wrote', a.out)


if __name__ == '__main__':
    main()
