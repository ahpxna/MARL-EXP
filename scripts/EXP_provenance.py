"""Provenance stamp for experiment outputs.

A JSON full of numbers is not re-evaluable unless it says which code produced it.
The script *name* is not enough: scripts get edited, and three of this
programme's experiments were rewritten after producing output that looked fine.
So every run records the hash of its own source, the repository state, the
library versions, and the command line.

`stamp(__file__)` returns a dict to merge into the output.
"""
import hashlib
import os
import platform
import subprocess
import sys
import time


def _sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def _git(*args):
    try:
        return subprocess.run(['git'] + list(args), capture_output=True,
                              text=True, timeout=10).stdout.strip() or None
    except Exception:
        return None


def versions():
    out = {'python': sys.version.split()[0], 'platform': platform.platform()}
    for name in ('numpy', 'scipy', 'mpmath'):
        try:
            mod = __import__(name)
            out[name] = getattr(mod, '__version__', 'unknown')
        except Exception:
            pass
    return out


def stamp(script_path, extra=None):
    p = os.path.abspath(script_path)
    d = {
        'script_path': os.path.relpath(p, os.getcwd()),
        'script_sha256': _sha256(p),
        'script_mtime_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ',
                                          time.gmtime(os.path.getmtime(p))),
        'run_started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        'argv': sys.argv[1:],
        'git_commit': _git('rev-parse', 'HEAD'),
        'git_branch': _git('rev-parse', '--abbrev-ref', 'HEAD'),
        'git_dirty': bool(_git('status', '--porcelain')),
        'versions': versions(),
    }
    if extra:
        d.update(extra)
    return d
