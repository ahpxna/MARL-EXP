"""Regenerate the ADAPTIVE search table from the current sweep."""
import json
import pathlib
from fractions import Fraction as F

SRC = pathlib.Path('research/paper_exp_20260916/adaptive_bigsearch.json')
OUT = pathlib.Path('research/papers/_tex/adaptive_search.tex')


def frac(s):
    f = F(s)
    return r'\frac{%d}{%d}' % (f.numerator, f.denominator) if f.denominator != 1 else str(f.numerator)


def main():
    d = json.loads(SRC.read_text())
    top = d['top'][:10]
    pk = d['per_K']
    Ks = sorted(int(k) for k in pk)
    L = [r'\begin{table}[htbp]',
         r'\caption{The ten worst targets found by exhaustive search over rational targets on',
         r'$%d\le K\le%d$ arms with denominators up to $%s$, run to horizon $%d$. Of $%s$ targets'
         % (Ks[0], Ks[-1], d['denominators'].split('..')[-1], d['horizon'],
            f"{d['targets_checked']:,}"),
         r'checked, $%s$---$%.1f\%%$---drive the largest-deficit rule past the bound of one. The'
         % (f"{d['targets_violating_quota']:,}", 100 * d['violation_fraction']),
         r'worst deficit is $%s$ and the earliest violation occurs at $t=%d$. A horizon bound can'
         % (frac(d['worst_deficit']), d['earliest_violation']),
         r'only understate: every count here is a lower bound on the count over unbounded',
         r'horizons. \NUM{}}',
         r'\label{tab:search}', r'\centering', r'\footnotesize',
         r'\setlength{\tabcolsep}{4pt}',
         r'\begin{tabular}{@{}clrrr@{}}', r'\toprule',
         r'$K$ & target $w$ & worst $D$ & value & first $t$ \\', r'\midrule']
    for r in top:
        ws = ',\\,'.join('$'.join(['', frac(x), '']).strip('$') for x in r['w'])
        ws = ',\\,'.join(frac(x) for x in r['w'])
        L.append(r'%d & $(%s)$ & $%s$ & %.4f & %d \\'
                 % (r['K'], ws, frac(r['worst']), r['worst_float'], r['first_violation']))
    L += [r'\bottomrule', r'\end{tabular}', '', r'\medskip', '',
          r'\begin{tabular}{@{}rrrrrr@{}}', r'\toprule',
          r'$K$ & targets & violating & fraction & worst $D$ & earliest $t$ \\', r'\midrule']
    for K in Ks:
        v = pk[str(K)]
        L.append(r'%d & %s & %s & %.3f & %s & %s \\'
                 % (K, f"{v['checked']:,}", f"{v['violating']:,}",
                    v['fraction'] or 0.0,
                    ('$%s$' % frac(v['worst_exact'])) if v['worst_exact'] else '---',
                    v['earliest'] if v['earliest'] is not None else '---'))
    L += [r'\bottomrule', r'\end{tabular}', r'\end{table}']
    OUT.write_text('\n'.join(L) + '\n')
    print('wrote', OUT)
    print('checked', d['targets_checked'], 'violating', d['targets_violating_quota'],
          'frac', round(d['violation_fraction'], 4), 'worst', d['worst_deficit'],
          'earliest', d['earliest_violation'])


if __name__ == '__main__':
    main()
