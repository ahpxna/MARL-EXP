"""Read-only replay of G14 receipts and F5-related exact witnesses; no solver/build."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/Users/phanan/cig-amf-main')

def read(rel):
    return json.loads((ROOT / rel).read_text())

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    status = read('research/worker_G14_status_20260915/G14_audit_closure_status.json')
    modules = sorted({m for row in status['rows'] for m in row['modules']})
    checks = []
    for m in modules:
        base = ROOT / 'work/p13_conjectures' / m
        src = base.with_suffix('.lean')
        rec = json.loads(base.with_suffix('.compile.receipt.json').read_text())
        log = base.with_suffix('.compile.log').read_text()
        ol = base.with_suffix('.olean')
        lists = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log, re.S)
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        result = {
            'module': m,
            'source_sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
            'audit_count': len(lists),
            'receipt_accepted_exit_zero': rec.get('accepted') is True and rec.get('lean_exit') == 0,
            'hash_matches': rec.get('source_sha256_before') == hashlib.sha256(src.read_bytes()).hexdigest(),
            'olean_fresh': ol.exists() and ol.stat().st_mtime >= src.stat().st_mtime,
            'logs_clean': not bool(re.search(r': error:|sorryAx|Lean.ofReduceBool', log)),
            'axioms_clean': bool(lists) and all(set(x.strip() for x in a.split(',') if x.strip()) <= allowed for a in lists),
        }
        result['pass'] = all(result[k] for k in ['receipt_accepted_exit_zero', 'hash_matches', 'olean_fresh', 'logs_clean', 'axioms_clean'])
        checks.append(result)

    # Explicit world, all unit variances. First two cells are the incumbent.
    mean = [F(-1,2), F(1,2), F(1,4), F(-1,4), F(-1,10), F(-1,30), F(1,30), F(1,10)]
    w = [F(1,5)] * 4 + [F(3,50), F(1,25), F(1,25), F(3,50)]
    pairs = []
    for a in range(2,8):
        for b in range(2,8):
            if a == b:
                continue
            v = (1 - mean[a] + mean[b])**2 / (2 * (1/w[0] + 1/w[1] + 1/w[a] + 1/w[b]))
            pairs.append({'a':a, 'b':b, 'pair_bound':str(v), 'at_least_1_over_160': v >= F(1,160)})
    alt = [F(-3,8), F(3,8), F(3,8), F(-3,8)] + mean[4:]
    energy = sum(we * (y-x)**2 / 2 for we,x,y in zip(w,mean,alt))
    old = F(49,8397)
    witness = {
        'means':list(map(str,mean)), 'weights':list(map(str,w)),
        'budget':str(sum(w)), 'pairs':pairs, 'alternative':list(map(str,alt)),
        'incumbent_range':str(abs(alt[1]-alt[0])),
        'outsider_range':str(max(alt[2:])-min(alt[2:])),
        'new_exact_value':str(energy), 'wstar_exact_value':str(old),
        'strict_gap':str(energy-old), 'ratio':str(energy/old),
        'scope':'Closed/tie flipping alternatives in the two-cell-incumbent range model; not the global optimum.',
    }
    assert sum(w)==1 and min(w)>0 and all(r['at_least_1_over_160'] for r in pairs)
    assert energy == F(1,160) and energy > old
    assert abs(alt[1]-alt[0]) <= max(alt[2:])-min(alt[2:])

    p26 = read('research/worker_P26_functional_20260915/P26_functional_contrast_cost.json')
    budget_rows = []
    for r in p26['rows']:
        k=r['K']; setup=F(str(r['setup_per_channel']))
        budget_rows.append({'K':k,'setup':str(setup),
          'raw_A_budget':str(1-setup*(k-1)), 'raw_C_budget':str(1-setup*k),
          'C_setup_exceeds_budget':setup*k>1,
          'D_over_C_at_variance_4':r['D_over_C_by_variance']['4.0'],
          'reported_A_over_C':r['A_over_C']})
    p24 = read('research/worker_P24_d6_20260915/P24_d6_boundary_modulus.json')
    out = {
       'audit_scope':'G14 named-module receipts and selected semantic/math checks; no clean rebuild or optimizers run',
       'g14_counts':status['counts'],
       'not_closed_rows':[{k:r[k] for k in ['id','status','verdict']} for r in status['rows'] if r['status']!='CLOSED'],
       'module_checks':checks, 'unique_modules':len(checks), 'audit_prints':sum(r['audit_count'] for r in checks),
       'all_receipt_checks_pass':all(r['pass'] for r in checks),
       'functional_nonoptimal_wstar_exact':witness,
       'P26_budget_and_variance_checks':budget_rows,
       'P24':{'cells':len(p24['cells']), 'all_left_tests_pass_as_recorded':all(r['test_from_left'] for r in p24['cells']),
               'right_test_warning':'Right-endpoint propagation needs a modulus for the FULL primal support, not the two-class support. Current outputs also pass the left test. Powers and endpoint values are stored as floats, so this is not an exact replay.'},
       'preregistration_scope':'No historical preregistration certified by this replay. A fresh hash/timestamp cannot establish that past results were preregistered.'
    }
    path=Path(args.out)
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as f:
        json.dump(out,f,indent=2)
        f.write('\n')
    print(json.dumps({'out':str(path),'modules':len(checks),'audits':out['audit_prints'],'receipts_pass':out['all_receipt_checks_pass'],'exact_improvement':str(energy-old)}))

if __name__ == '__main__':
    main()
