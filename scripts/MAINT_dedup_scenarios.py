#!/usr/bin/env python3
"""Hard-link identical CityFlow scenario files (user-approved 01/10/2026 09:1x EDT; disk full).

Scope: roadnet.json and flow.json inside directories named `scenarios/` under research/marl_budget (the per-evaluation
copies that every evaluator regenerates deterministically from the traffic seed).  config.json is NOT touched (it holds
the run's own path).  No content is removed: every path keeps a file with byte-identical content; duplicates merely share
one inode.  For each duplicate: byte-compare with the canonical copy (filecmp, shallow=False), link the canonical copy
to a temporary name in the duplicate's directory, then os.replace() it over the duplicate (atomic; the path never
disappears).  Any mismatch or error leaves that file untouched and is logged.
Log: research/marl_budget/dedup_scenarios_20261001.log.gz (one line per linked file) + summary on stdout.
Usage: python -u scripts/MAINT_dedup_scenarios.py [--dry-run]
"""
from __future__ import annotations
import filecmp, gzip, hashlib, os, sys, time
from collections import defaultdict

R = 'research/marl_budget'; LOG = f'{R}/dedup_scenarios_20261001.log.gz'; DRY = '--dry-run' in sys.argv


def main():
    t0 = time.time(); groups = defaultdict(list)
    for dp, dn, fn in os.walk(R):
        if '/scenarios/' not in dp + '/':
            continue
        for f in fn:
            if f in ('roadnet.json', 'flow.json'):
                p = os.path.join(dp, f); groups[(f, os.path.getsize(p))].append(p)
    print(f'scan {sum(map(len, groups.values()))} files in {time.time()-t0:.0f}s', flush=True)
    linked = skipped = errors = 0; freed = 0; done_groups = 0
    log = None if DRY else gzip.open(LOG, 'wt')
    for (f, size), paths in groups.items():
        if len(paths) < 2:
            continue
        byh = defaultdict(list)
        for p in paths:
            with open(p, 'rb') as fh:
                byh[hashlib.sha256(fh.read()).hexdigest()].append(p)
        for h, ps in byh.items():
            ps.sort(); canon = ps[0]; ci = os.stat(canon).st_ino
            for p in ps[1:]:
                try:
                    if os.stat(p).st_ino == ci:
                        skipped += 1; continue
                    if not filecmp.cmp(canon, p, shallow=False):
                        errors += 1; print(f'MISMATCH (left untouched): {p}', flush=True); continue
                    if not DRY:
                        tmp = p + '.dedup_tmp'
                        os.link(canon, tmp); os.replace(tmp, p)
                        log.write(f'{p}\t{canon}\t{h}\n')
                    linked += 1; freed += size
                except Exception as e:      # leave the file as it was
                    errors += 1; print(f'ERROR {p}: {e}', flush=True)
                    if not DRY and os.path.exists(p + '.dedup_tmp'):
                        os.replace(p + '.dedup_tmp', p + '.dedup_tmp_orphan')
        done_groups += 1
        if done_groups % 200 == 0:
            print(f'{done_groups} groups, linked {linked}, freed {freed/2**30:.2f} GiB, {time.time()-t0:.0f}s', flush=True)
    if log:
        log.close()
    print(f'{"DRY RUN " if DRY else ""}DONE linked {linked} files, already-linked {skipped}, errors {errors}, '
          f'freed {freed/2**30:.2f} GiB in {time.time()-t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
