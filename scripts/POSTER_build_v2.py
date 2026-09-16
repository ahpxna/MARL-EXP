#!/usr/bin/env python3
"""Build a poster from COMPUTED geometry.

The template supplies the design -- fonts, colours, the header bar, the logo -- and this
script supplies the content and the positions.  Shapes are cloned from the template's own
shapes when a column needs more blocks than the template happens to have, so the
typography is always the template's and never invented here.
"""
import argparse, copy, json
from pathlib import Path
from pptx import Presentation
from pptx.oxml.ns import qn
from pptx.util import Emu
from pptx.oxml.ns import qn as _qn
from lxml.etree import SubElement
from pptx.oxml import parse_xml


def OxmlElement(tag):
    ns = 'http://schemas.openxmlformats.org/drawingml/2006/main'
    return parse_xml(f'<a:{tag.split(":")[1]} xmlns:a="{ns}"/>')

TEMPLATE = 'Poster Template (1) (2) (1).pptx'
# template shapes to borrow typography from, by role
ROLE_SOURCE = {'header': 22, 'prose': 20, 'caption': 15}
TITLE_SHAPE = 0
LOGO_SHAPE = 10


def set_text(shape, lines):
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


def set_autofit(shape, scale):
    """Let PowerPoint shrink the text to the box instead of clipping it.

    The box geometry is computed, so a column that carries more than its natural share
    should render smaller rather than overflow; `normAutofit` is exactly that behaviour and
    it is what the template's own boxes would do if the content grew.
    """
    bodyPr = shape.text_frame._txBody.find(qn('a:bodyPr'))
    if bodyPr is None:
        return
    for tag in ('a:normAutofit', 'a:spAutoFit', 'a:noAutofit'):
        el = bodyPr.find(qn(tag))
        if el is not None:
            bodyPr.remove(el)
    af = OxmlElement('a:normAutofit')
    af.set('fontScale', str(int(max(25, min(100, scale)) * 1000)))
    af.set('lnSpcReduction', str(int(max(0, min(20, (100 - scale) * 0.4)) * 1000)))
    bodyPr.append(af)


def place(shape, box):
    shape.left = Emu(int(box['left'] * 914400))
    shape.top = Emu(int(box['top'] * 914400))
    shape.width = Emu(int(box['width'] * 914400))
    shape.height = Emu(int(box['height'] * 914400))


def build(layout_path, meta_path, out_path):
    layout = json.loads(Path(layout_path).read_text())
    meta = json.loads(Path(meta_path).read_text())
    out = Path(out_path)
    if out.exists():
        raise SystemExit(f'Refusing to overwrite {out}')

    prs = Presentation(TEMPLATE)
    slide = prs.slides[0]
    shapes = list(slide.shapes)
    spTree = slide.shapes._spTree

    # title first, from the template's own title box
    set_text(shapes[TITLE_SHAPE], meta['title'])

    # everything except the title and the logo is replaced by computed blocks
    keep = {TITLE_SHAPE, LOGO_SHAPE}
    sources = {role: copy.deepcopy(shapes[idx]._element) for role, idx in ROLE_SOURCE.items()}
    for i, sh in enumerate(shapes):
        if i in keep:
            continue
        sh._element.getparent().remove(sh._element)

    counts = {'header': 0, 'prose': 0, 'caption': 0, 'eq': 0, 'fig': 0}
    fills = {c: layout['report'][c]['fill'] for c in ('1', '2', '3')}
    eq_index = json.loads(Path('research/papers/_figures/eq/index.json').read_text())
    for col in ('1', '2', '3'):
        # a column carrying more than its natural share renders smaller, never clipped
        fontscale = 100.0 if fills[col] <= 1.0 else 100.0 / fills[col]
        for box in layout['boxes'][col]:
            k = box['kind']
            if k in ('header', 'prose', 'caption'):
                el = copy.deepcopy(sources[k])
                spTree.append(el)
                sh = slide.shapes[-1]
                set_text(sh, box['lines'] if box['lines'] else [box.get('text') or ''])
                place(sh, box)
                set_autofit(sh, fontscale)
            elif k == 'eq':
                slide.shapes.add_picture(
                    eq_index[box['ref']]['path'],
                    Emu(int(box['left'] * 914400)), Emu(int(box['top'] * 914400)),
                    width=Emu(int(box['width'] * 914400)),
                    height=Emu(int(box['height'] * 914400)))
            elif k == 'fig':
                slide.shapes.add_picture(
                    box['ref'],
                    Emu(int(box['left'] * 914400)), Emu(int(box['top'] * 914400)),
                    width=Emu(int(box['width'] * 914400)),
                    height=Emu(int(box['height'] * 914400)))
            counts[k] += 1

    out.parent.mkdir(parents=True, exist_ok=True)
    prs.save(str(out))
    print(f'poster written: {out}')
    for k, v in counts.items():
        print(f'  {k:9}: {v}')
    for col, rep in layout['report'].items():
        print(f'  column {col} fill {rep["fill"]:.3f}  {rep["verdict"]}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('layout')
    ap.add_argument('--meta', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    build(a.layout, a.meta, a.out)


if __name__ == '__main__':
    main()
