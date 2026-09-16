"""Re-run an experiment and check it reproduces its committed output exactly.

A seed in the header is a claim, not a guarantee: a run that draws in a
different order, or that depends on dictionary iteration or on a library
default, will quietly produce different numbers from the same seed. This
re-runs a script into a scratch file and compares the result with the output
already on disk, ignoring only the provenance block and the wall clock.

Usage: EXP_verify_repro.py <script> <existing.json> [-- extra args]
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

IGNORE = {'provenance', 'wall_seconds'}


def prune(x):
    if isinstance(x, dict):
        return {k: prune(v) for k, v in x.items() if k not in IGNORE}
    if isinstance(x, list):
        return [prune(v) for v in x]
    return x


def first_difference(a, b, path='$'):
    if type(a) is not type(b):
        return f'{path}: type {type(a).__name__} vs {type(b).__name__}'
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a:
                return f'{path}.{k}: missing in the re-run'
            if k not in b:
                return f'{path}.{k}: missing in the original'
            d = first_difference(a[k], b[k], f'{path}.{k}')
            if d:
                return d
        return None
    if isinstance(a, list):
        if len(a) != len(b):
            return f'{path}: length {len(a)} vs {len(b)}'
        for i, (x, y) in enumerate(zip(a, b)):
            d = first_difference(x, y, f'{path}[{i}]')
            if d:
                return d
        return None
    if a != b:
        return f'{path}: {a!r} vs {b!r}'
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('script')
    ap.add_argument('existing')
    ap.add_argument('extra', nargs=argparse.REMAINDER)
    a = ap.parse_args()
    extra = [x for x in a.extra if x != '--']
    with tempfile.NamedTemporaryFile(suffix='.json', delete=False) as tf:
        tmp = tf.name
    cmd = [sys.executable, a.script, '--out', tmp] + extra
    print('re-running:', ' '.join(cmd), flush=True)
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        print('RE-RUN FAILED\n', r.stdout[-2000:], r.stderr[-2000:])
        sys.exit(1)
    old = prune(json.loads(Path(a.existing).read_text()))
    new = prune(json.loads(Path(tmp).read_text()))
    diff = first_difference(old, new)
    if diff is None:
        # keep the stamped re-run: same numbers, better provenance
        Path(a.existing).write_text(Path(tmp).read_text())
        print(f'REPRODUCES EXACTLY -> {a.existing} replaced with the stamped re-run')
    else:
        print('DIFFERS at', diff)
        print('re-run left at', tmp)
        sys.exit(2)


if __name__ == '__main__':
    main()
