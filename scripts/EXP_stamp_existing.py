"""Attach provenance to experiment outputs that were written before stamping.

Re-running a long sweep only to record a hash would be silly, but leaving the
outputs unidentified is worse. This records, for each JSON, the hash of the
script that bears its name *and* whether that script has been modified since the
JSON was written. The second field is the one that matters: if the script was
touched afterwards, the hash is the current code rather than the code that ran,
and the only honest thing to do is say so and re-run when it matters.

Nothing already in a file is overwritten; the block is added under
`provenance`, and a file that already has one is left alone unless --force.
"""
import argparse
import json
import os
import pathlib
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as P

OUT = pathlib.Path('research/paper_exp_20260916')
SCRIPTS = pathlib.Path('scripts')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()
    rows = []
    for p in sorted(OUT.glob('*.json')):
        try:
            d = json.loads(p.read_text())
        except Exception as e:
            print(f'{p.name}: UNREADABLE ({e})')
            continue
        if 'provenance' in d and not a.force:
            print(f'{p.name}: already stamped')
            continue
        name = d.get('script')
        sp = SCRIPTS / name if name else None
        if not (sp and sp.exists()):
            prov = {'script_named_in_file': name, 'script_found': False,
                    'note': 'the named script is not present; this output cannot be '
                            'reproduced without recovering it'}
        else:
            json_mtime = p.stat().st_mtime
            script_mtime = sp.stat().st_mtime
            modified_after = script_mtime > json_mtime
            prov = P.stamp(str(sp))
            prov.pop('run_started_utc', None)
            prov.pop('argv', None)
            prov.update({
                'stamped_retroactively': True,
                'output_written_utc': __import__('time').strftime(
                    '%Y-%m-%dT%H:%M:%SZ', __import__('time').gmtime(json_mtime)),
                'script_modified_after_this_run': bool(modified_after),
                'note': ('the script was edited after this output was written, so the '
                         'hash above is NOT the code that produced it -- re-run before '
                         'relying on this file')
                if modified_after else
                        ('the script has not been modified since this output was '
                         'written, so the hash above identifies the code that ran'),
            })
        d['provenance'] = prov
        p.write_text(json.dumps(d, indent=1))
        flag = prov.get('script_modified_after_this_run')
        rows.append((p.name, flag))
        print(f'{p.name}: stamped'
              + ('  *** SCRIPT CHANGED SINCE RUN ***' if flag else ''))
    stale = [n for n, f in rows if f]
    print(f'\n{len(rows)} stamped; {len(stale)} with a script changed since the run')
    for n in stale:
        print('  stale:', n)


if __name__ == '__main__':
    main()
