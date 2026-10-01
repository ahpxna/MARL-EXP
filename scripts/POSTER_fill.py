"""Tune a poster until every column is full, and report what it did.

The layout tool already reports each column's fill; nothing was acting on it.
Total content is set so the three columns sum to just under three, and long
prose is split into paragraph-sized blocks so the balancer has somewhere to cut
-- one 2000-character block cannot be divided between two columns, which is what
left a third of the sheet blank while another column overflowed.
"""
import json
import re
import subprocess
import sys
import pathlib
import importlib.util
import copy

_s = importlib.util.spec_from_file_location('pf', 'scripts/POSTER_from_paper.py')
PF = importlib.util.module_from_spec(_s); _s.loader.exec_module(PF)
PAPER = {'MASTER': 'master', 'QUERY': 'query', 'STRUCTURAL': 'structural',
         'FUNCTIONAL': 'functional', 'D6': 'd6', 'SUPPORT': 'support',
         'ADAPTIVE': 'adaptive'}

TARGET_LO, TARGET_HI = 2.94, 3.00
MIN_PARA = 200
CAP = 520


def split_long(blocks, cap=CAP):
    """Break an over-long prose block at sentence boundaries."""
    out = []
    for x in blocks:
        if x.get('kind') != 'prose':
            out.append(x); continue
        t = ' '.join(x.get('lines') or [])
        if len(t) <= cap:
            out.append(x); continue
        sents = re.split(r'(?<=[.!?])\s+', t)
        cur, parts = '', []
        for s in sents:
            if len(cur) + len(s) + 1 > cap and len(cur) >= MIN_PARA:
                parts.append(cur.strip()); cur = s
            else:
                cur = (cur + ' ' + s).strip()
        if cur:
            parts.append(cur)
        for p in parts:
            y = dict(x); y['lines'] = [p]
            out.append(y)
    return out


def fills(d):
    b = pathlib.Path('research/papers') / d
    subprocess.run([sys.executable, 'scripts/POSTER_layout.py', str(b / 'blocks.json'),
                    '--out', str(b / 'layout.json')], capture_output=True)
    r = json.loads((b / 'layout.json').read_text())['report']
    return [r[c]['fill'] for c in '123'], [r[c]['text_scale'] for c in '123']


def trim_longest(blocks, frac=0.12):
    """Shorten the longest prose block by dropping its last sentences."""
    # the longest block is often a single long sentence, which cannot be cut
    # without rewriting it; choose the longest block that has something to drop
    cand = [i for i, x in enumerate(blocks) if x.get('kind') == 'prose'
            and len(re.split(r'(?<=[.!?])\s+', ' '.join(x['lines']))) > 1]
    if not cand:
        return False
    idx = max(cand, key=lambda i: len(' '.join(blocks[i]['lines'])))
    t = ' '.join(blocks[idx]['lines'])
    sents = re.split(r'(?<=[.!?])\s+', t)
    keep = max(1, int(len(sents) * (1 - frac)))
    if keep >= len(sents):
        keep = len(sents) - 1
    if keep < 1:
        return False
    blocks[idx]['lines'] = [' '.join(sents[:keep])]
    return True


def pool(d):
    """Sentences from the paper's Results that the poster does not carry yet."""
    name = PAPER[d.split('_')[0]]
    txt = PF.results(name) or ''
    have = ' '.join(' '.join(x.get('lines') or [])
                    for x in json.loads((pathlib.Path('research/papers') / d /
                                         'blocks.json').read_text()))
    out = []
    for sent in re.split(r'(?<=[.!?])\s+', txt):
        if len(sent) > 60 and sent[:50] not in have:
            out.append(sent)
    return out


def add_from_paper(blocks, spare, n=3):
    """Append more of the paper's Results under the Results header."""
    if not spare:
        return False
    take, spare[:] = spare[:n], spare[n:]
    proto = copy.deepcopy(next(x for x in blocks if x.get('kind') == 'prose'))
    proto['lines'] = [' '.join(take)]
    ri = [i for i, x in enumerate(blocks) if x.get('kind') == 'header'
          and 'result' in ' '.join(x.get('lines') or []).lower()]
    if not ri:
        return False
    j = next((i for i in range(ri[0] + 1, len(blocks))
              if blocks[i].get('kind') == 'header'), len(blocks))
    blocks.insert(j, proto)
    return True


def moves(blocks):
    """Candidate reorderings: each figure, to each later or earlier section break.

    Columns must be contiguous, so the balancer cannot move content across a
    boundary on its own: if column 3 is thin while column 1 overflows, the fix is
    to reorder the blocks, not to cut text the paper wrote. A figure is the
    largest movable unit and the least tied to its neighbours.
    """
    figs = [i for i, x in enumerate(blocks) if x.get('kind') == 'fig']
    heads = [i for i, x in enumerate(blocks) if x.get('kind') == 'header']
    out = []
    for i in figs:
        n = 2 if (i + 1 < len(blocks) and blocks[i + 1].get('kind') == 'caption') else 1
        pair = blocks[i:i + n]
        rest = blocks[:i] + blocks[i + n:]
        for h in heads:
            t = h - n if h > i else h
            if 0 <= t < len(rest) and not (i - 2 <= t <= i + 1):
                out.append(rest[:t + 1] + pair + rest[t + 1:])
    return out


def tune(d, rounds=120):
    p = pathlib.Path('research/papers') / d / 'blocks.json'
    b = split_long(json.loads(p.read_text()))
    p.write_text(json.dumps(b, indent=1))
    spare = pool(d)
    for _ in range(rounds):
        f, ts = fills(d)
        if max(f) <= 1.005 and sum(f) >= TARGET_LO:
            return f, ts, 'filled'
        if max(f) > 1.005:
            # reorder before cutting: try each placement and keep the best
            best, score = None, max(f)
            for cand in moves(b)[:40]:
                p.write_text(json.dumps(cand, indent=1))
                cf, _ = fills(d)
                if max(cf) < score - 0.004:
                    best, score = cand, max(cf)
            if best is not None:
                b = best
                p.write_text(json.dumps(b, indent=1))
                continue
            p.write_text(json.dumps(b, indent=1))
            if not trim_longest(b, 0.30 if sum(f) > 3.10 else 0.15):
                break
            p.write_text(json.dumps(b, indent=1))
        else:
            if not add_from_paper(b, spare):
                return f, ts, f'under target, paper text exhausted'
            b = split_long(b)
            p.write_text(json.dumps(b, indent=1))
    f, ts = fills(d)
    return f, ts, 'stopped'


if __name__ == '__main__':
    for d in sys.argv[1:]:
        f, ts, why = tune(d)
        print(f'{d.split("_")[0]:11s} fill {f[0]:.2f}/{f[1]:.2f}/{f[2]:.2f}  '
              f'body {25*ts[0]:.0f}/{25*ts[1]:.0f}/{25*ts[2]:.0f} pt  sum {sum(f):.2f}  {why}')
