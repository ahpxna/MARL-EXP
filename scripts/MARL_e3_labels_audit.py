#!/usr/bin/env python3
"""Key-level integrity audit of E3 continuation-label directories (28/09 independent recheck, resume/provenance closure).

The resumable producers (v2, v3) keep every COMPLETE line of every partial file, deduplicate by (episode, t) with the
LAST copy winning, and reset their failure list; the final manifest's self_check therefore covers only the states of
the last attempt.  This audit does not assume any of that is harmless.  Per label directory:
  files      every labels.partial_<k>.jsonl.gz and labels.jsonl.gz, decompressed with a streaming decoder that stops
             at a truncation: complete lines, a trailing partial line (bytes), JSON errors in the MIDDLE (corruption);
  keys       expected keys from the producer arguments (manifest args, or the first watchdog command in the log):
             episodes of the split x headways 8/16, [:limit], [shard::nshards], x snaps.  Reported: missing and
             extraneous keys in the loader-visible file (labels.jsonl.gz), duplicate keys inside it, and every key
             that appears in any partial file but not in labels.jsonl.gz (a LOST line);
  conflicts  for every key present in several files, the canonical JSON (sorted keys) of every copy: identical,
             or CONFLICT (different content);
  records    semantic checks: candidate 0 is the prefix of (order, K); every candidate legal (|S_i| = k_i, i not in
             S_i) and distinct; stored bytes == profile_cost; cont values finite; joint actions in range;
  self-checks  every per-state line of every attempt in the log ("<episode> t<t>: ... fails <n>"): the cumulative
             failure count must not increase at any state; each final key must have a production line with no new
             failure (else its self-check provenance is UNKNOWN); SELF-CHECK FAIL / Traceback lines are listed;
  producers  the producer script of each watchdog attempt, and the attempt that printed each final key.
A directory written by ONE attempt without resume (no partial files, manifest self_check PASS, no resumed states) is
covered by its manifest even when its per-state log lines are elsewhere.
Exit code 1 if any hard defect (missing/extraneous/lost/conflict/duplicate/record/self-check) is found.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, math, re, sys, zlib
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import prefix_sets, profile_cost

SPLITS = {'train': range(301, 365), 'select': range(401, 409), 'dev': range(501, 509)}
LINE = re.compile(r'\] (seed\d+_load[\d.]+) t(\d+): .* fails (\d+)$')
ATTEMPT = re.compile(r'\[watchdog\] attempt (\d+) (.+?): .*?scripts/(MARL_e3_continuation_labels\w*\.py) (.*)$')


def read_lines(f):
    raw = f.read_bytes(); d = zlib.decompressobj(16 + zlib.MAX_WBITS); out = b''; err = None
    try:
        out = d.decompress(raw)
        if not d.eof:
            err = 'gzip stream truncated (no end marker)'
    except zlib.error as e:
        err = f'zlib error: {e}'
    text = out.decode('utf-8', errors='replace'); lines = text.split('\n'); tail = lines.pop()
    recs, mid_err = [], []
    for n, l in enumerate(lines):
        try:
            recs.append(json.loads(l))
        except json.JSONDecodeError as e:
            mid_err.append((n, str(e)[:80]))
    return recs, dict(complete_lines=len(recs), trailing_partial_bytes=len(tail.encode()), stream=err or 'complete', json_errors_mid=mid_err)


def canon(r):
    return hashlib.sha256(json.dumps(r, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def args_of(L):
    man = L / 'manifest.json'
    if man.exists():
        a = json.loads(man.read_text())['args']; return dict(split=a['split'], snaps=a['snaps'], limit=a['limit'], shard=a['shard'], nshards=a['nshards'])
    for lf in (Path(str(L) + '.log'), Path(str(L) + '.v3.log')):
        if lf.exists():
            for l in lf.read_text(errors='replace').splitlines():
                if '[watchdog] attempt' in l and '--split' in l:
                    tok = l.split(); g = lambda k, d=None: tok[tok.index(k) + 1] if k in tok else d
                    sn = []; i = tok.index('--snaps') + 1
                    while i < len(tok) and not tok[i].startswith('--'):
                        sn.append(int(tok[i])); i += 1
                    return dict(split=g('--split'), snaps=sn, limit=int(g('--limit', 0)), shard=int(g('--shard', 0)), nshards=int(g('--nshards', 1)))
    raise SystemExit(f'{L}: producer arguments unknown')


def expected(sp):
    eps = [(s, h) for s in SPLITS[sp['split']] for h in (8.0, 16.0)]
    if sp['limit']:
        eps = eps[:sp['limit']]
    eps = eps[sp['shard']::sp['nshards']]
    return {(f'seed{s}_load{h:g}', t) for s, h in eps for t in sp['snaps']}


def record_check(r):
    bad = []; m = r['m']; P = [sorted(s) for s in prefix_sets(r['order'], r['K'])]
    if [sorted(s) for s in r['cands'][0]['sets']] != P:
        bad.append('candidate 0 is not the prefix')
    seen = set()
    for c in r['cands']:
        S = c['sets']; key = tuple(tuple(sorted(s)) for s in S)
        if key in seen:
            bad.append('duplicate candidate'); break
        seen.add(key)
        if any(len(S[i]) != r['K'][i] or i in S[i] for i in range(m)):
            bad.append('illegal candidate'); break
        if c['bytes'] != profile_cost(r['order'], r['K'], [set(s) for s in S])[0]:
            bad.append('bytes != profile_cost'); break
        if not all(math.isfinite(c[k]) for k in ('cont', 'cont_1')) or len(c['joint']) != m or not all(0 <= x < 9 for x in c['joint']):
            bad.append('bad cont/joint'); break
    return bad


def log_audit(L):
    logs = [p for p in (Path(str(L) + '.log'), Path(str(L) + '.v3.log')) if p.exists()]
    prod = {}; attempts = []; fail_lines = []; cur = None; last_fails = 0
    for lf in logs:
        for l in lf.read_text(errors='replace').splitlines():
            m_ = ATTEMPT.search(l)
            if m_:
                cur = dict(log=lf.name, attempt=int(m_.group(1)), time=m_.group(2), producer=m_.group(3)); attempts.append(cur); last_fails = 0; continue
            if 'SELF-CHECK FAIL' in l or l.startswith('Traceback') or 'Error' in l[:40]:
                fail_lines.append(f'{lf.name}: {l[:120]}')
            m_ = LINE.search(l)
            if m_ and cur is not None:
                n = int(m_.group(3)); key = (m_.group(1), int(m_.group(2)))
                prod[key] = dict(producer=cur['producer'], time=cur['time'], new_failure=n > last_fails); last_fails = n
    return prod, attempts, fail_lines


def audit(L):
    sp = args_of(L); exp = expected(sp); files = sorted(L.glob('labels.partial_*.jsonl.gz'), key=lambda p: int(p.name.split('_')[1].split('.')[0]))
    cur = L / 'labels.jsonl.gz'; rep = dict(dir=str(L), complete=(L / 'manifest.json').exists(), spec=sp, expected_keys=len(exp), files={})
    copies = defaultdict(set); final = {}; final_dups = 0
    for f in files + ([cur] if cur.exists() else []):
        recs, info = read_lines(f); rep['files'][f.name] = info
        for r in recs:
            k = (r['episode_id'], r['t']); h = canon(r); copies[k].add(h)
            if f == cur:
                final_dups += k in final; final[k] = (h, r)
    fk = set(final); partial_keys = set(copies)
    prod, attempts, fail_lines = log_audit(L)
    rec_bad = {f'{k[0]} t{k[1]}': b for k, (h, r) in final.items() if (b := record_check(r))}
    no_prod = sorted(k for k in fk if k not in prod); new_fail = sorted(k for k in fk if prod.get(k, {}).get('new_failure'))
    by_prod = defaultdict(int)
    for k in fk:
        by_prod[prod[k]['producer'] if k in prod else 'UNKNOWN'] += 1
    rep.update(final_keys=len(fk), missing=len(exp - fk) if rep['complete'] else None, pending=len(exp - fk), extraneous=sorted(map(list, fk - exp))[:10],
               lost_from_partials=sorted(map(list, partial_keys - fk))[:10], n_lost=len(partial_keys - fk), final_duplicate_keys=final_dups,
               conflicts=sorted(f'{k[0]} t{k[1]}' for k, hs in copies.items() if len(hs) > 1)[:10], n_conflicts=sum(len(hs) > 1 for hs in copies.values()),
               record_defects=dict(list(rec_bad.items())[:10]), n_record_defects=len(rec_bad), attempts=attempts, final_keys_by_producer=dict(by_prod),
               keys_without_production_line=len(no_prod), keys_with_new_failure=len(new_fail), failure_lines=fail_lines[:10])
    hard = bool(rep['extraneous'] or rep['n_lost'] or rep['final_duplicate_keys'] or rep['n_conflicts'] or rep['n_record_defects'] or new_fail
                or (rep['complete'] and rep['missing']) or any(v['json_errors_mid'] for v in rep['files'].values()))
    man = json.loads((L / 'manifest.json').read_text()) if rep['complete'] else {}
    single = bool(rep['complete'] and not files and man.get('self_check') == 'PASS' and not man.get('resumed_states'))
    rep['single_attempt_manifest_covers_all'] = single          # one attempt, no resume: the manifest's self_check covers every key
    rep['verdict'] = 'DEFECT' if hard else ('PASS' if (not no_prod or single) else 'PASS (self-check provenance UNKNOWN for some keys)')
    return rep


def main(a):
    reps = []
    for pat in a.dirs:
        for L in sorted(Path('.').glob(pat)):
            if L.is_dir() and L.name.startswith('labels'):
                r = audit(L); reps.append(r)
                print(f'{r["verdict"]:10s} {r["dir"]}: final {r["final_keys"]}/{r["expected_keys"]} (pending {r["pending"]}) lost {r["n_lost"]} conflicts {r["n_conflicts"]} '
                      f'dups {r["final_duplicate_keys"]} extraneous {len(r["extraneous"])} record-defects {r["n_record_defects"]} | producers {r["final_keys_by_producer"]} '
                      f'| no-log-line {r["keys_without_production_line"]} new-fail {r["keys_with_new_failure"]} | files ' +
                      ' '.join(f'{n}:{v["complete_lines"]}{"" if v["stream"] == "complete" else "(trunc)"}' for n, v in r['files'].items()), flush=True)
    Path(a.out).write_text(json.dumps(reps, indent=1, default=str))
    sys.exit(1 if any(r['verdict'] == 'DEFECT' for r in reps) else 0)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('dirs', nargs='+'); p.add_argument('--out', required=True); main(p.parse_args())
