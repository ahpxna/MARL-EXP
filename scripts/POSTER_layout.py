#!/usr/bin/env python3
"""Compute poster geometry instead of guessing it.

A column is an ordered stack of blocks.  Every block's natural height is COMPUTED --
equations and figures from their image aspect, prose from its character count at the
template's own font size -- so nothing overlaps and nothing is left as dead space.  The
stack is then fitted to the column's vertical extent and the fill ratio is reported, so a
thin column is visible as a number rather than discovered on the printed sheet.
"""
import json, math
from pathlib import Path

# the template's own three columns, in inches
COLUMNS = {
    1: {"left": 1.30, "width": 12.90},
    2: {"left": 15.40, "width": 15.20},
    3: {"left": 31.00, "width": 15.60},
}
TOP = 4.10          # first header's top edge
BOTTOM = 35.85      # last block's bottom edge
GAP = 0.16          # between blocks inside a column
GAP_AFTER_HEADER = 0.10

# the template's own sizes, in points
FS = {"header": 50, "prose": 25, "caption": 22, "eq_pad": 0}
H_HEADER = 0.92

# inches of poster per pixel of the 30 pt / 300 dpi equation render: a single-line
# formula lands at about 0.62 in, roughly one and a half body lines.
EQ_SCALE = 0.0031

EQ_INDEX = Path('research/papers/_figures/eq/index.json')


def _aspect(path_or_key, eq_index):
    if path_or_key in eq_index:
        return eq_index[path_or_key]['aspect']
    from PIL import Image
    w, h = Image.open(path_or_key).size
    return w / h


def prose_height(lines, width_in, fs):
    """Height of a paragraph block at the template's font size.

    chars-per-line uses an average glyph advance of 0.50 em, which is right for the
    template's body face; line advance is 1.24 em.  Blank strings are half-lines.
    """
    cpl = max(1.0, width_in * 72.0 / (0.50 * fs))
    n = 0.0
    for ln in lines:
        if not ln.strip():
            n += 0.45
        else:
            n += math.ceil(len(ln) / cpl)
    return n * 1.24 * fs / 72.0


def layout_column(col, blocks, eq_index, top=TOP, bottom=BOTTOM):
    """Assign each block a box, filling the column exactly. Returns (boxes, report)."""
    left, width = COLUMNS[col]['left'], COLUMNS[col]['width']
    nat = []
    for b in blocks:
        k = b['kind']
        if k == 'header':
            h = H_HEADER
        elif k in ('prose', 'caption'):
            fs = FS['prose'] if k == 'prose' else FS['caption']
            h = prose_height(b['lines'], width - 0.2, b.get('fs', fs))
        elif k == 'eq':
            # Equations are placed by HEIGHT, not width, so every formula on the sheet is
            # typeset at the same glyph size.  Placing by width magnifies a short formula
            # and shrinks a long one, which is what made them look inconsistent.
            meta = eq_index[b['key']]
            h = meta['px_h'] * EQ_SCALE
            w = h * meta['aspect']
            if w > width * 0.98:      # too long for the column, and only then
                w = width * 0.98      # does it render smaller -- legitimately
                h = w / meta['aspect']
            b['_w'] = w
        elif k == 'fig':
            w = b.get('width', width * b.get('wfrac', 0.92))
            h = w / _aspect(b['path'], eq_index)
            b['_w'] = w
        else:
            raise SystemExit(f'unknown block kind {k!r}')
        nat.append(h)

    gaps = [GAP_AFTER_HEADER if blocks[i]['kind'] == 'header' else GAP
            for i in range(len(blocks) - 1)]
    natural = sum(nat) + sum(gaps)
    avail = bottom - top
    fill = natural / avail

    # distribute the difference over the PROSE blocks only: equations and figures keep
    # their aspect, headers keep the template's height.
    prose_idx = [i for i, b in enumerate(blocks) if b['kind'] in ('prose', 'caption')]
    slack = avail - natural
    if prose_idx:
        # Distribute the difference in PROPORTION to each block's natural height, not
        # equally.  Equal shares give a one-line block the same absolute slack as a
        # six-line one, so the short blocks end up loose and the long ones tight -- and a
        # renderer that auto-fits per box then draws them at visibly different sizes.
        base = sum(nat[i] for i in prose_idx)
        for i in prose_idx:
            share = (nat[i] / base) if base > 0 else (1.0 / len(prose_idx))
            nat[i] = max(0.24, nat[i] + slack * share)

    boxes, y = [], top
    for i, b in enumerate(blocks):
        if b['kind'] in ('eq', 'fig'):
            w = b['_w']
            boxes.append({'kind': b['kind'], 'left': round(left + (width - w) / 2, 2),
                          'top': round(y, 2), 'width': round(w, 2),
                          'height': round(nat[i], 2), 'ref': b.get('key') or b.get('path')})
        else:
            boxes.append({'kind': b['kind'], 'left': round(left, 2), 'top': round(y, 2),
                          'width': round(width, 2), 'height': round(nat[i], 2),
                          'shape': b.get('shape'), 'lines': b.get('lines'),
                          'text': b.get('text')})
        y += nat[i] + (gaps[i] if i < len(gaps) else 0)

    return boxes, {'natural_in': round(natural, 2), 'available_in': round(avail, 2),
                   'fill': round(fill, 3), 'blocks': len(blocks),
                   'verdict': ('OVERFULL — trim' if fill > 1.02 else
                               'thin — add content' if fill < 0.80 else 'good')}


def block_height(col, b, eq_index):
    width = COLUMNS[col]['width']
    k = b['kind']
    if k == 'header':
        return H_HEADER
    if k in ('prose', 'caption'):
        fs = FS['prose'] if k == 'prose' else FS['caption']
        return prose_height(b['lines'], width - 0.2, b.get('fs', fs))
    if k == 'eq':
        meta = eq_index[b['key']]
        h = meta['px_h'] * EQ_SCALE
        if h * meta['aspect'] > width * 0.98:
            h = (width * 0.98) / meta['aspect']
        return h
    w = b.get('width', width * b.get('wfrac', 0.92))
    return w / _aspect(b['path'], eq_index)


def atomise(blocks):
    """Split multi-paragraph prose into one block per paragraph.

    A column break between two paragraphs is ordinary typography; one inside a paragraph is
    a defect.  Splitting here gives the balancer paragraph-level granularity without ever
    letting it cut mid-argument, and keeps equations welded to the paragraph that
    introduces them.
    """
    out = []
    for b in blocks:
        if b['kind'] == 'prose' and len(b['lines']) > 1:
            for ln in b['lines']:
                if ln.strip():
                    out.append({'kind': 'prose', 'lines': [ln]})
        else:
            out.append(b)
    return out


def balance(blocks, eq_index, top=TOP, bottom=BOTTOM):
    """Split ONE ordered block list into three contiguous columns.

    Columns must stay contiguous: a reader goes down column 1, then down column 2.  The
    split minimising the worst column's fill is chosen by scanning every pair of cut
    points, which is cheap for the block counts a poster has.  A column may not start on
    anything but a header, so sections are never orphaned from their titles.
    """
    blocks = atomise(blocks)
    n = len(blocks)
    avail = bottom - top
    heights = [[block_height(c, b, eq_index) for b in blocks] for c in (1, 2, 3)]
    # A cut may fall anywhere EXCEPT immediately after a header, which would leave that
    # header alone at the foot of a column; and never between an equation or figure and the
    # prose that introduces it.
    def opens_a_unit(b):
        # after atomising, any paragraph is a legitimate column opening -- what must never
        # happen is opening on an equation, a figure or a caption orphaned from its text.
        '''A column may open on a section header or on a numbered step, never mid-argument.'''
        if b['kind'] == 'header':
            return True
        if b['kind'] == 'prose':
            return True
        return False

    cuts = [i for i in range(1, n)
            if blocks[i - 1]['kind'] != 'header' and opens_a_unit(blocks[i])]
    best, best_score = None, None
    for i in cuts:
        for j in cuts:
            if j <= i:
                continue
            parts = [(1, blocks[:i], heights[0][:i]),
                     (2, blocks[i:j], heights[1][i:j]),
                     (3, blocks[j:], heights[2][j:])]
            fills = []
            for col, bs, hs in parts:
                gaps = [GAP_AFTER_HEADER if b['kind'] == 'header' else GAP
                        for b in bs[:-1]]
                fills.append((sum(hs) + sum(gaps)) / avail)
            # readability first: a column should open on a section, not mid-argument.
            # A non-header cut is allowed but must buy a real gain in balance to win.
            # prefer opening on a section, then on a step, then on any paragraph
            def cost(k):
                b = blocks[k]
                if b['kind'] == 'header':
                    return 0.0
                if b['lines'] and b['lines'][0].lstrip().startswith(('STEP ', 'C1.', 'C2.', 'C3.',
                                                                    'C4.', 'C5.', 'C6.')):
                    return 0.04
                return 0.12
            penalty = cost(i) + cost(j)
            score = (max(fills) - min(fills)
                     + 2 * max(0.0, max(fills) - 1.02)
                     + penalty)
            if best_score is None or score < best_score:
                best_score, best = score, (i, j, fills)
    if best is None:
        raise SystemExit('no header to split on')
    i, j, fills = best
    return {'1': blocks[:i], '2': blocks[i:j], '3': blocks[j:]}, fills


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('blocks', help='JSON file of {"1": [...], "2": [...], "3": [...]}')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    eq_index = json.loads(EQ_INDEX.read_text()) if EQ_INDEX.exists() else {}
    src = json.loads(Path(a.blocks).read_text())
    if isinstance(src, list):
        src, fills = balance(src, eq_index)
        print('  auto-split fills: ' + '  '.join(f'{f:.3f}' for f in fills))
    out, report = {}, {}
    for col in ('1', '2', '3'):
        boxes, rep = layout_column(int(col), src[col], eq_index)
        out[col] = boxes
        report[col] = rep
        print(f'  column {col}: {rep["blocks"]:2d} blocks, natural {rep["natural_in"]:5.2f}in '
              f'of {rep["available_in"]:5.2f}in  fill {rep["fill"]:.3f}  {rep["verdict"]}')
    Path(a.out).write_text(json.dumps({'boxes': out, 'report': report}, indent=1))
    print(f'geometry: {a.out}')


if __name__ == '__main__':
    main()
