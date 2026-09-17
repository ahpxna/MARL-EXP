#!/usr/bin/env python3
"""Write a paper's poster into the user's own PowerPoint template.

The template's layout, fonts, colours, logo and shape geometry are left untouched: only
the TEXT of each shape and the BYTES of each picture are replaced, so the output is the
same poster design with this paper's content in it.
"""
import argparse, copy, json
from pathlib import Path
from pptx import Presentation
from pptx.oxml.ns import qn
from pptx.util import Emu

TEMPLATE = 'Poster Template (1) (2) (1).pptx'


def set_text(shape, lines):
    """Replace a text box's content.

    Paragraph `i` of the template keeps its own formatting for line `i`; extra lines clone
    the last template paragraph that actually carries a run, so the box's typography --
    which belongs to the user's template, not to this script -- survives intact.
    """
    body = shape.text_frame._txBody
    paras = body.findall(qn('a:p'))
    formatted = [q for q in paras if q.findall(qn('a:r'))]
    filler = formatted[-1] if formatted else (paras[0] if paras else None)
    if filler is None:
        raise SystemExit('text box has no paragraph to clone')
    for q in paras:
        body.remove(q)
    for i, line in enumerate(lines):
        src = paras[i] if i < len(paras) and paras[i].findall(qn('a:r')) else filler
        q = copy.deepcopy(src)
        for br in q.findall(qn('a:br')):
            q.remove(br)
        runs = q.findall(qn('a:r'))
        runs[0].find(qn('a:t')).text = line
        for r in runs[1:]:
            q.remove(r)
        body.append(q)


def replace_picture(shape, png_path):
    """Swap the bytes behind a picture, leaving its frame and position alone."""
    part = shape.part.related_part(shape._element.blip_rId)
    part._blob = Path(png_path).read_bytes()


def build(spec_path, out_path):
    spec = json.loads(Path(spec_path).read_text())
    out = Path(out_path)
    if out.exists():
        raise SystemExit(f'Refusing to overwrite {out}')
    prs = Presentation(TEMPLATE)
    shapes = list(prs.slides[0].shapes)

    for idx_s, lines in spec['text'].items():
        idx = int(idx_s)
        if not shapes[idx].has_text_frame:
            raise SystemExit(f'shape {idx} has no text frame')
        set_text(shapes[idx], lines)

    for idx_s, png in spec.get('pictures', {}).items():
        idx = int(idx_s)
        if not Path(png).exists():
            raise SystemExit(f'missing figure {png}')
        replace_picture(shapes[idx], png)

    for idx_s, box in spec.get('geometry', {}).items():
        sh = shapes[int(idx_s)]
        if 'left' in box:   sh.left   = int(box['left'] * 914400)
        if 'top' in box:    sh.top    = int(box['top'] * 914400)
        if 'width' in box:  sh.width  = int(box['width'] * 914400)
        if 'height' in box: sh.height = int(box['height'] * 914400)

    eq_index = {}
    eq_idx_path = Path('research/papers/_figures/eq/index.json')
    if eq_idx_path.exists():
        eq_index = json.loads(eq_idx_path.read_text())
    placed = 0
    for key, box in spec.get('equations', {}).items():
        if key not in eq_index:
            raise SystemExit(f'equation {key!r} has not been rendered; run POSTER_equations.py')
        meta = eq_index[key]
        w = box['width']
        h = w / meta['aspect']
        prs.slides[0].shapes.add_picture(
            meta['path'], Emu(int(box['left'] * 914400)), Emu(int(box['top'] * 914400)),
            width=Emu(int(w * 914400)), height=Emu(int(h * 914400)))
        placed += 1

    for idx_s in spec.get('delete', []):
        sh = shapes[int(idx_s)]
        sh._element.getparent().remove(sh._element)

    out.parent.mkdir(parents=True, exist_ok=True)
    prs.save(str(out))
    print(f'poster written: {out}')
    print(f'  text shapes replaced : {len(spec["text"])}')
    print(f'  figures replaced     : {len(spec.get("pictures", {}))}')
    print(f'  equations typeset    : {placed}')
    print(f'  shapes resized       : {len(spec.get("geometry", {}))}')
    print(f'  shapes removed       : {len(spec.get("delete", []))}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    build(a.spec, a.out)


if __name__ == '__main__':
    main()
