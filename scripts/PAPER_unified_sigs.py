#!/usr/bin/env python3
"""Extract the Lean statements of the unified-batch modules into `sigs.json`.

The appendix generator renders whatever is in `sigs.json`, so the statements it
prints must come from the source the prover accepted, not from a hand-written
list.  This script reads the `.lean` files directly and records, for each
`theorem`/`lemma`, the declaration header exactly as written, with the proof
removed and nothing else changed.
"""

import json
import pathlib
import re
import sys

SIGS_PATH = ('/private/tmp/claude-502/-Users-phanan-cig-amf-main/'
             '53cb7f6c-fbe2-4b96-92c8-1e901e01194d/sigs.json')
SRC = pathlib.Path('work/p13_conjectures')

MODULES = [
    'LeanUnifiedSupportExchangeV1',
    'LeanUnifiedCompressionDecisionV1',
    'LeanUnifiedQueryOrderV1',
    'LeanUnifiedObstructionOrderV1',
    'LeanUnifiedStructuralRelaxedV1',
    'LeanUnifiedGeometryBoundV1',
]

DECL = re.compile(r'^(private\s+)?(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_\']*)')


def namespace_of(text):
    m = re.search(r'^namespace\s+(\S+)', text, re.M)
    return m.group(1) if m else ''


def extract(path):
    """Return the list of theorem/lemma records in `path`.

    The proof begins at the first `:=` that sits at parenthesis depth zero;
    a `:=` inside brackets is Lean's named-argument syntax, part of the
    statement, and must not be mistaken for the start of the proof."""
    text = path.read_text()
    ns = namespace_of(text)
    lines = text.split('\n')
    out, i = [], 0
    while i < len(lines):
        m = DECL.match(lines[i])
        if not m:
            i += 1
            continue
        kind, name = m.group(2), m.group(3)
        buf, j, depth, done = [], i, 0, False
        while j < len(lines) and not done:
            ln = lines[j]
            keep, k = [], 0
            while k < len(ln):
                ch = ln[k]
                if ch in '([{':
                    depth += 1
                elif ch in ')]}':
                    depth -= 1
                elif ch == ':' and k + 1 < len(ln) and ln[k + 1] == '=' and depth == 0:
                    done = True
                    break
                keep.append(ch)
                k += 1
            buf.append(''.join(keep).rstrip())
            j += 1
        sig = ' '.join(x.strip() for x in buf if x.strip())
        sig = re.sub(r'\s+', ' ', sig).strip()
        if sig.startswith('private '):
            sig = sig[len('private '):]
        out.append({'name': name,
                    'full': f'{ns}.{name}' if ns else name,
                    'kind': kind,
                    'file': str(path),
                    'sig': sig})
        i = j
    return out


def main():
    sigs = json.load(open(SIGS_PATH))
    total = 0
    for mod in MODULES:
        p = SRC / f'{mod}.lean'
        if not p.exists():
            print(f'  MISSING {p}', file=sys.stderr)
            return 1
        recs = [r for r in extract(p) if not r['name'].startswith('_')]
        sigs[mod] = recs
        total += len(recs)
        print(f'  {mod:36s} {len(recs):3d} statements')
    json.dump(sigs, open(SIGS_PATH, 'w'), indent=1)
    print(f'\n{total} statements written into sigs.json across {len(MODULES)} modules')
    return 0


if __name__ == '__main__':
    sys.exit(main())
