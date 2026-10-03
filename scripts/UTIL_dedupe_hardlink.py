#!/usr/bin/env python3
"""Reclaim disk WITHOUT deleting anything (02/10/2026 02:3x; E4 lanes refused at 14 GB free): byte-identical scenario files
(the deterministic CityFlow dumps every evaluation and trainer writes again under <run>/scenarios*/seed*_load*/) are replaced
by HARD LINKS to one copy.  Every path stays, with exactly the same bytes; only duplicate storage is released.
Scope: files under a directory whose name starts with 'scenarios' inside a run directory that is FINISHED (has
manifest.json) or lies under legacy/ (never a live run).  Identity = size + SHA-256, then a full byte comparison before
linking; the link is made atomically (os.link to a temporary name, then os.replace).  Every replacement is recorded in
<log> (path, canonical path, sha256, size).  --dry-run measures only.
Usage: UTIL_dedupe_hardlink.py --log research/marl_budget/dedupe_<date>.jsonl [--dry-run] [--min-bytes 65536] ROOT..."""
from __future__ import annotations
import argparse, filecmp, hashlib, json, os, sys, time
from pathlib import Path


def finished_run(p: Path, roots):
    for q in [p] + list(p.parents):
        if (q / 'manifest.json').exists():
            return True
        if q.name == 'legacy':
            return True
        if any(q == r for r in roots):
            return False
    return False


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def main(a):
    roots = [Path(r).resolve() for r in a.roots]; groups = {}; n = 0
    for r in roots:
        for dp, dn, fn in os.walk(r):
            d = Path(dp)
            if not any(part.startswith('scenarios') for part in d.relative_to(r).parts):
                continue
            for x in fn:
                p = d / x
                try:
                    st = p.lstat()
                except FileNotFoundError:
                    continue
                if not p.is_file() or p.is_symlink() or st.st_size < a.min_bytes:
                    continue
                groups.setdefault(st.st_size, []).append(p); n += 1
    print(f'{n} candidate files', flush=True)
    saved = 0; links = 0; logf = None if a.dry_run else open(a.log, 'a')
    run_ok = {}
    for size, ps in groups.items():
        if len(ps) < 2:
            continue
        byhash = {}
        for p in ps:
            key = p.parent
            if key not in run_ok:
                run_ok[key] = finished_run(p.parent, roots)
            if run_ok[key]:
                try:
                    byhash.setdefault(sha(p), []).append(p)
                except OSError:                                  # moved / removed meanwhile (e.g. parked to legacy/)
                    continue
        for h, qs in byhash.items():
            if len(qs) < 2:
                continue
            try:
                qs.sort(key=lambda p: (p.stat().st_ino))
                canon = qs[0]; ci = canon.stat().st_ino
            except OSError:
                continue
            for q in qs[1:]:
                try:
                    st = q.stat()
                    if st.st_ino == ci:
                        continue
                    if st.st_dev != canon.stat().st_dev or not filecmp.cmp(canon, q, shallow=False):
                        continue
                    if not a.dry_run:
                        tmp = q.with_name(q.name + '.dedupe_tmp')
                        os.link(canon, tmp); os.replace(tmp, q)
                        logf.write(json.dumps(dict(path=str(q), canonical=str(canon), sha256=h, size=size, time=time.ctime())) + '\n')
                except OSError:                                  # a path moved meanwhile: left as it is
                    continue
                if st.st_nlink == 1:
                    saved += size
                links += 1
    if logf:
        logf.close()
    print(f'{"would link" if a.dry_run else "linked"} {links} files; {"would free" if a.dry_run else "freed"} ≈ {saved / 2**30:.2f} GB', flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('roots', nargs='+'); ap.add_argument('--log', required=True); ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--min-bytes', type=int, default=65536)
    main(ap.parse_args())
