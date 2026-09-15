#!/usr/bin/env python3
"""Read-only checks of the worker handoff; writes a separate audit artifact.
No experiment or Lean process is launched. Existing evidence is never rewritten.
"""
from __future__ import annotations
import argparse, datetime, hashlib, json, math, re, statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PRIMARY = ['LeanD6ReferenceResponseJoinV1', 'LeanStructuralToleranceQuantifiersV1',
           'LeanSupportObstructionQueryOrderV1']
SUPPLEMENTARY = ['LeanD6ReferencePhaseValueV1', 'LeanD6ReferencePhaseThresholdV1']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def lean_audit(name):
    base = ROOT / 'work/p13_conjectures'
    s, l, o = [base / (name + ext) for ext in ['.lean', '.compile.log', '.olean']]
    source, log = s.read_text(), l.read_text()
    audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
    declared = re.findall(r'^#print axioms\s+(\S+)', source, re.M)
    parsed = [{'declaration': n, 'axioms': sorted(x.strip() for x in a.split(',') if x.strip())}
              for n, a in audits]
    checks = {
        'no_logged_errors': not re.search(r'\berror:', log),
        'all_printed_audits_present': len(parsed) == len(declared) and
            sorted(x['declaration'].split('.')[-1] for x in parsed) == sorted(declared),
        'axioms_allowed': bool(parsed) and all(set(x['axioms']) <= ALLOWED for x in parsed),
        'olean_exists_and_newer_than_source': o.exists() and o.stat().st_mtime_ns >= s.stat().st_mtime_ns,
        'log_newer_than_source': l.stat().st_mtime_ns >= s.stat().st_mtime_ns,
        'no_placeholder_tokens_in_source': not re.search(r'\b(sorry|admit|native_decide)\b', source),
    }
    rp = base / (name + '.compile.receipt.json')
    receipt = json.loads(rp.read_text()) if rp.exists() else None
    if receipt:
        checks['receipt_exit_zero_and_source_hash_matches'] = (
            receipt.get('lean_exit') == 0 and receipt.get('source_sha256_at_launch') == sha(s))
    return {'module': name, 'checks': checks, 'passes_record_checks': all(checks.values()),
            'source_sha256': sha(s), 'log_sha256': sha(l), 'olean_sha256': sha(o) if o.exists() else None,
            'olean_bytes': o.stat().st_size if o.exists() else None, 'audit_count': len(parsed),
            'audit_declarations': parsed, 'receipt': receipt,
            'warnings': [x for x in log.splitlines() if re.search(r'\.lean:\d+:\d+: warning:', x)],
            'scope': 'Existing build records plus theorem/source review, not a clean rebuild; mtime alone is not source-byte provenance.'}

def median_interval(vals):
    n = len(vals); tail = 0; k = 0
    for candidate in range(1, n // 2 + 1):
        tail += math.comb(n, candidate - 1)
        if tail / (2 ** n) <= .025: k = candidate
        else: break
    if k == 0: return {'n': n, 'interval': None}
    ordered = sorted(vals)
    return {'n': n, 'one_based_order_indices': [k, n-k+1], 'interval': [ordered[k-1], ordered[n-k]],
            'meaning': 'Distribution-free interval for the median of recorded capped times; endpoints at H+1 remain censored.'}

def functional_audit(path):
    d = json.loads(path.read_text()); rows = d['runs_by_variant']; H = d['max_n'] + 1
    maps = {v: {(x['seed'], x['instance_id']): x for x in rr} for v, rr in rows.items()}
    keys = set(maps['uniform']); checks = {}
    checks['unique_equal_paired_keys'] = all(len(rows[v]) == len(maps[v]) and set(maps[v]) == keys for v in rows)
    checks['same_world_hash_all_policies'] = checks['unique_equal_paired_keys'] and all(
        len({maps[v][key]['world_sha256'] for v in rows}) == 1 for key in keys)
    summaries = {}
    for v, rr in rows.items():
        vals = [H if x['N_certificate'] is None else x['N_certificate'] for x in rr]
        summary = {'n':len(rr), 'certificate_fraction':sum(x['certificate_emitted'] for x in rr)/len(rr),
                   'median_N_certificate':statistics.median(vals),
                   'restricted_mean_censored_N_certificate':statistics.mean(vals),
                   'false_safe_count':sum(x['false_safe'] is True for x in rr)}
        checks[v+'_summary_matches_raw'] = all(math.isclose(summary[k], d['by_variant'][v][k], rel_tol=1e-12, abs_tol=1e-12)
                                               for k in summary if k != 'n')
        checks[v+'_censoring_consistent'] = all(
            (x['N_certificate'] is not None) == x['certificate_emitted'] and x['censored_N_certificate'] == nv
            and (x['N_certificate'] is None or 0 < x['N_certificate'] <= d['max_n']) for x,nv in zip(rr,vals))
        if v in d['deployable_variants']:
            checks[v+'_no_oracle_flags'] = all(not x['known_sigma_used'] and not x['known_extrema_used'] for x in rr)
        summary['median_interval_95'] = median_interval(vals)
        summaries[v] = summary
    pairs = {}
    for other in ['uniform','C_anytime','C_extrema_oracle']:
        counts = {k:0 for k in ['both','lucb_only','other_only','neither','win','loss','tie']}; ratios = []
        for key in keys:
            a, b = maps['C_lucb'][key]['N_certificate'], maps[other][key]['N_certificate']
            if a is not None and b is not None:
                counts['both'] += 1; counts['win' if a < b else 'loss' if a > b else 'tie'] += 1; ratios.append(b/a)
            else: counts['lucb_only' if a is not None else 'other_only' if b is not None else 'neither'] += 1
        n = counts['win'] + counts['loss']
        p = min(1., 2*sum(math.comb(n,i) for i in range(min(counts['win'],counts['loss'])+1))/(2**n)) if n else None
        pairs[other] = {**counts, 'conditional_median_other_over_lucb': statistics.median(ratios) if ratios else None,
                        'conditional_ratio_interval_95':median_interval(ratios) if ratios else None,
                        'two_sided_sign_p_conditional_on_both_certify': p,
                        'scope': 'Paired test is conditional on both certifying; not a population domination theorem.'}
    fp = path.with_suffix('.freeze.json'); freeze = json.loads(fp.read_text()) if fp.exists() else None
    provenance = {'freeze_present': freeze is not None}
    if freeze:
        runner = ROOT / freeze['runner_surface']['runner_file']
        checks['artifact_hash_matches_freeze'] = sha(path) == freeze.get('artifact_sha')
        provenance.update({'freeze_sha256_current_file':sha(fp), 'exit_code':freeze.get('exit_code'),
                           'source_changed_during_run':freeze.get('source_changed_during_run'),
                           'runner_sha_changed_during_run':freeze.get('runner_sha_changed_during_run'),
                           'runner_current_matches_launch':sha(runner)==freeze['runner_surface']['runner_sha'],
                           'limit':'Endpoint runner hashes do not prove absence of temporary edits or dependency changes; whole-tree dirty hash includes untracked outputs.'})
    return {'input':str(path.relative_to(ROOT)), 'input_sha256':sha(path), 'seeds':d['seeds'],
            'total_runs':sum(len(rr) for rr in rows.values()), 'checks':checks, 'passes_checks':all(checks.values()),
            'raw_recomputed':summaries, 'paired_lucb':pairs, 'world_audit':d['world_audit'],
            'artifact_admissibility_label':d.get('admissibility'), 'provenance':provenance,
            'scope':'Reanalysis of existing observations, not a rerun or an independent confirmatory experiment.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--artifact',default='research/confirm_ieee_20260912/functional_v4_lucb_dev_cellv1.json')
    p.add_argument('--out',default='research/high_risk_20260910/worker_handoff_audit_20260912.json');a=p.parse_args()
    path=ROOT/a.artifact;out=ROOT/a.out
    if out.exists(): raise SystemExit('Refusing to overwrite an existing audit; choose a new --out.')
    result={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'script_sha256':sha(Path(__file__)), 'lean_primary':[lean_audit(n) for n in PRIMARY],
            'lean_additional_algebraic':[lean_audit(n) for n in SUPPLEMENTARY], 'functional':functional_audit(path)}
    result['passes_record_checks']=all(x['passes_record_checks'] for x in result['lean_primary']+result['lean_additional_algebraic']) and result['functional']['passes_checks']
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2,ensure_ascii=False,allow_nan=False)+'\n')
    print(json.dumps({'out':str(out),'primary_audits':sum(x['audit_count'] for x in result['lean_primary']),
                      'additional_algebraic_audits':sum(x['audit_count'] for x in result['lean_additional_algebraic']),
                      'raw_runs':result['functional']['total_runs'],'passes':result['passes_record_checks']}))
    return 0 if result['passes_record_checks'] else 1
if __name__=='__main__':raise SystemExit(main())
