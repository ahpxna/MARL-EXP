#!/usr/bin/env python3
"""TSI poster v4 (09/10/2026): the user's Google Slides version ('Staged Upgrades of Two Learned Populations (1).pptx', 06/10 08:34,
10 x 5.625 in) updated to the evidence of 09/10 (W15-W20, field checks) and re-laid out for print.
Content edits are in TEXT (shape index of the user's file -> (bold lead, body)); typography is the user's (Times New Roman; headers 10 pt,
body 5 pt, captions 4 pt on the 10-in slide); every column is restacked top to bottom from MEASURED text heights (Times New Roman metrics,
greedy wrap at the box width minus insets and bullet indent), so blocks neither overlap nor leave gaps; spare height goes to the figures.
Two passes: pass 1 uses estimated heights and writes <out>.pos.json (each text block's top and the next block's top); the caller renders
it (LibreOffice), measure_pdf() reads the real text extents, and pass 2 rebuilds with those heights (--heights JSON).
Usage: POSTER_tsi_v4.py <in pptx> <fig3 png> <out pptx> [--heights JSON]  |  POSTER_tsi_v4.py measure <pdf> <pos json> <out heights json>"""
import copy, json, sys
from pathlib import Path
from lxml import etree
from PIL import ImageFont
from pptx import Presentation
from pptx.util import Emu, Inches, Pt

A = '{http://schemas.openxmlformats.org/drawingml/2006/main}'
TNR = '/System/Library/Fonts/Supplemental/Times New Roman.ttf'; TNRB = '/System/Library/Fonts/Supplemental/Times New Roman Bold.ttf'
F = {False: ImageFont.truetype(TNR, 1000), True: ImageFont.truetype(TNRB, 1000)}
EMU = 914400; LINE = 1.17                     # line height / font size (Times New Roman ascent + descent + gap, 100 % spacing)
TOP, BOTTOM = 0.80, 5.52; GAP, GAP_H, GAP_CAP = 0.045, 0.035, 0.012
HEADER_PT, BODY_PT, CAP_PT, REF_PT = 10.0, 5.0, 4.0, 3.7; H_HEADER = 0.165

TEXT = {
    4: ("Fig. 1.  The upgrade erases a learned fleet's benefit.",
        ' Against its own base driver the fleet saves fuel under fixed-time signals (blue). Under a learned signal without timing it is its base driver (grey, zero by construction); with the old timing served as SPaT it loses fuel and time (orange).'),
    5: ('Context.',
        ' Every stop at a red light wastes fuel. Connected cars can avoid stops when the light broadcasts when it will turn green (signal phase and timing, SPaT): they ease off early and glide through. Both the lights and these driving aids are now becoming AI, owned by different parties, cities and carmakers, and upgraded separately.'),
    6: ('The trouble starts when one side is upgraded.',
        " In simulation (SUMO, a 16-light grid), an AI eco-driving fleet saves 6.5% fuel under fixed-cycle lights, but the saving vanishes once the lights become AI-controlled (Fig. 1); publishing a forecast of the new light costs the fleet's cars time."),
    7: ('Why.',
        ' Learned lights usually count a car as waiting only once it has stopped (below 0.1 m/s), the default in sumo-rl [10] and RESCO [11]. A car gliding on SPaT never counts, so the light serves it later. We keep both AIs frozen and change only what the fleet is told and what the light senses.'),
    9: ('Prior work repairs one side.',
        " SPaT prediction for adaptive signals [1, 2] and GLOSA at highly adaptive lights [3] improve the forecast; eco-driving under uncertain or actuated timing [4, 5] changes the vehicle; joint control and FoRL [6], which trains a signal to forecast and keep its own actions, retrain a policy; DC-Ada [7] adapts a frozen policy's inputs by reward-only search."),
    10: ('',
        "The failure is a self-defeating forecast, as in anticipatory route guidance [8] and performative prediction [9]; here the fleet's reaction passes through the signal's own input (Fig. 2)."),
    13: ('Fig. 2.  The loop and the two interfaces TSI changes (blue).',
        " Published timing makes agents glide; a halting-count signal stops counting them, holds its green, and the forecast's own target moves (orange)."),
    48: ('Testbed.',
        ' A 16-signal grid (grid4), two lanes per direction; shared double-DQN keep/switch signals; a PPO eco-approach fleet on SPaT, half of all vehicles; 5 signals × 4 fleets × 20 fresh traffic seeds per confirmation.'),
    14: ('',
        'Four registered stages, decision rules fixed before confirmation: M1, a fleet worth protecting; M2, the upgrade removes its benefit; M3, a repair through the two interfaces alone; M4, transfer.'),
    16: ('Fleet side.',
        ' The old timing is replaced by a hybrid provider: exact when the timing is determined (a yellow whose next green serves the link), otherwise a state-conditioned quantile forecaster fitted to eight logged episodes of the deployed signal with a query-weighted pinball loss:'),
    18: ('Light side (TSI).',
        ' The frozen signal is made to count gliding cars: a speed-binned count in front of its halting-count input, with A = B = 0 the deployed signal. One setting, (A, B) = (1, 0.25), serves new signals, with no gradient step for either policy:'),
    'tsig': ('TSI-G: one sensing layer for any signal.',
        ' Each SPaT car is sensed as the human driver it replaces (free speed, braking, car following, a stop at the queue tail), and queues, waits and pressures are computed on these twins. One parameter, calibrated on ordinary traffic logs.'),
    20: ('Decision.',
        ' A repair passes only if fleet fuel falls and every time loss (city, fleet, human) stays below +0.5 s/veh at the one-sided upper bound of a crossed bootstrap over signal, fleet and traffic seeds, with no more teleports or unfinished trips:'),
    23: ('Why both sides.',
        " In a threshold-queue model where a fleet share ρ glides and the signal's input weights a glider by A, a forecast learned without the fleet errs by"),
    26: ('',
        'Underweighting gliders (A < 1) delays service beyond the forecast, more so the larger the fleet; A = 1 removes the bias. In a one-car model each one-sided repair provably fails and both together reach the optimum.'),
    30: ('Fig. 3.  Who pays for the forecast, and the repair.',
        " (A) Extra wait of the fleet's cars vs no SPaT (5 signals × 4 fleets × 20 fresh seeds; 95% intervals): TSI and TSI-G remove the penalty; signals that see speed or position need no repair. (B) Fleet fuel saved."),
    49: ('The repair works.',
        ' Registered confirmation: TSI cut fleet fuel by 3.85% (95% CI 3.26–4.43), every time loss within the limit. Its default setting, fixed in advance, saves 5.6% (HBEFA4) and 3.3% (PHEMlight5) on new signals and fleets, transfers to two more networks, and tolerates 80% detection and 20% message loss; ported DC-Ada and FoRL miss the limits.'),
    31: ('We pinpoint the cause: the stop threshold.',
        ' Trained by the same recipe, signals that see speed groups, queue positions or every vehicle (RESCO wave) need no repair: the forecast alone meets every limit and their greens do not lengthen. The finding holds when the reward or any scale constant is changed.'),
    33: ('TSI-G repairs the community defaults, without retraining.',
        " Forecast alone, the fleet's cars lose 5.4 s/veh under sumo-rl's default signal, 2.6 under RESCO's IDQN / IPPO state and 16.0 under its MPLight state; with TSI-G, −0.2, −0.2 and 0.5, and 5–10% fuel saved. On RL-H, TSI-G beats TSI (−0.3 s/veh)."),
    36: ('Fig. 4.  Mechanism.',
        " Under the service the learned signal holds its greens longer (A); the fleet's extra time grows with that lengthening (B); on a replayed schedule exact timing saves both fuel and time (C)."),
    37: ('A prediction made before the run held.',
        ' MaxPressure counts vehicles at every speed, so the model says the forecast alone should suffice: registered in advance, the fleet-side service alone met every limit (−2.68%) and the greens did not lengthen.'),
    'field': ('Checked against field data.',
        ' On real adaptive signals in Hamburg the forecaster holds its 0.1 quantile on held-out days; measured fuel (VED) supports PHEMlight5; on recorded Salt Lake City demand the fleet saves about 10% fuel.'),
    41: ('',
        "Calibrated simulation; a road pilot with a SPaT fleet is next. Each signal's forecaster uses its own logs, and TSI-G uses V2X to know which cars follow SPaT."),
    44: ('Bottom line.',
        ' AI lights and AI cars run by different owners depend on each other, and upgrading one can quietly break the other. The break runs through what the light counts; sensing each SPaT car as the human it replaces repairs it without retraining either AI.'),
    45: ('For cities and carmakers:',
        ' before deploying a learned light where cars use SPaT, check what it counts: stop counts need TSI or TSI-G; speed or position inputs work with the forecast alone.'),
}
REFS_ADD = (' [10] L. N. Alegre, "SUMO-RL," GitHub, 2019. [11] J. Ault, G. Sharon, "Reinforcement learning benchmarks for traffic signal control," '
            'NeurIPS Datasets and Benchmarks, 2021.')
HEADERS = {2: 'I.  Introduction', 8: 'Related Work', 11: 'II.  Methodology', 22: 'II.  Methodology, continued', 28: 'III.  Results', 34: 'IV.  Discussion',
           40: 'Limitations', 43: 'V.  Conclusions', 46: 'References', 'res2': 'III.  Results, continued'}
# column stacks (top to bottom); 'tsig' and 'res2' are new shapes cloned from 18 and 28
COLS = {1: [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 48],
        2: [22, 14, 16, 17, 18, 19, 'tsig', 20, 21, 23, 24, 26, 37, 28, 29, 30],
        3: ['res2', 49, 31, 33, 34, 35, 36, 'field', 40, 41, 43, 44, 45, 46, 47]}
X = {1: (0.27, 2.69), 2: (3.21, 3.17), 3: (6.46, 3.25)}
FIGS = {3: 1, 29: 2, 35: 3, 12: 1}; FIGMAXW = {3: 2.35}   # Fig. 1 not wider than in the user's layout             # resizable figures (picture shape -> column); equation pictures keep their size
DELETE = [32, 39, 15, 25, 42, 27, 38]


def measure(runs, width_in, size_pt, indent_in):
    """Lines of greedy word wrap for [(text, bold)] at size_pt in width_in (minus insets and indent)."""
    avail = (width_in - 2 * 17450 / EMU - indent_in) * 72.0 * 0.97; words = []
    for t, b in runs:
        for i, w in enumerate(t.split(' ')):
            words.append((w, b, i > 0 or t.startswith(' ')))
    lines, cur = 1, 0.0
    for w, b, sp in words:
        ww = F[b].getlength(w) / 1000 * size_pt; spw = F[b].getlength(' ') / 1000 * size_pt if sp and cur > 0 else 0.0
        if cur > 0 and cur + spw + ww > avail:
            lines += 1; cur = ww
        else:
            cur += spw + ww
    return lines


def text_height(runs, width_in, size_pt, indent_in):
    return measure(runs, width_in, size_pt, indent_in) * size_pt * LINE / 72.0 + 2 * 8725 / EMU


def set_runs(shape, runs, size_pt):
    p = shape.text_frame.paragraphs[0]; rs = p.runs; tb, tn = rs[0]._r.find(A + 'rPr'), (rs[1] if len(rs) > 1 else rs[0])._r.find(A + 'rPr')
    for extra in shape.text_frame.paragraphs[1:]:
        extra._p.getparent().remove(extra._p)
    for r in list(rs):
        p._p.remove(r._r)
    end = p._p.find(A + 'endParaRPr')
    for t, b in runs:
        if not t:
            continue
        r = etree.SubElement(p._p, A + 'r'); rp = copy.deepcopy(tb if b else tn); rp.set('b', '1' if b else '0'); rp.set('sz', str(int(size_pt * 100)))
        r.append(rp); te = etree.SubElement(r, A + 't'); te.text = t
        if end is not None:
            end.addprevious(r)
    bp = shape.text_frame._txBody.find(A + 'bodyPr')
    for a_, v_ in (('lIns', '17450'), ('rIns', '17450'), ('tIns', '8725'), ('bIns', '8725')):
        bp.set(a_, v_)
    for tag in ('spcBef', 'spcAft'):
        e_ = p._p.find(A + 'pPr').find(A + tag) if p._p.find(A + 'pPr') is not None else None
        if e_ is not None:
            for g_ in e_:
                g_.set('val', '0')
    for c in list(bp):
        bp.remove(c)
    etree.SubElement(bp, A + 'noAutofit')
    bu = p._p.find(A + 'pPr')
    if bu is not None and bu.find(A + 'buSzPts') is not None:
        bu.find(A + 'buSzPts').set('val', str(int(size_pt * 100)))


def clone(slide, shape):
    el = copy.deepcopy(shape._element); slide.shapes._spTree.append(el)
    ids = [int(x) for x in slide.shapes._spTree.xpath('.//p:cNvPr/@id')]; el.xpath('.//p:cNvPr')[0].set('id', str(max(ids) + 1))
    return slide.shapes[-1]


def main(src, fig3, out, heights=None):
    heights = heights or {}
    prs = Presentation(src); sl = prs.slides[0]; S = list(sl.shapes); sh = {i: s for i, s in enumerate(S)}
    sh['tsig'] = clone(sl, S[18]); sh['res2'] = clone(sl, S[28]); sh['field'] = clone(sl, S[37])
    # title: author, mentor
    tp = S[0].text_frame.paragraphs; auth = tp[2]; auth.runs[0].text = 'Vu Phan An Nguyen'
    for r in auth.runs[1:]:
        auth._p.remove(r._r)
    m = copy.deepcopy(auth._p); auth._p.addnext(m); mr = m.findall(A + 'r')[0]; mr.find(A + 't').text = 'Mentor: Dr. Jay Zhengping Luo'
    mr.find(A + 'rPr').set('b', '0'); m.find(A + 'pPr').find(A + 'spcBef').find(A + 'spcPts').set('val', '0')
    for q in (auth._p, m):
        q.find(A + 'pPr').find(A + 'lnSpc').find(A + 'spcPct').set('val', '100000')
    auth._p.find(A + 'pPr').find(A + 'spcBef').find(A + 'spcPts').set('val', '100')
    # headers
    for k, t in HEADERS.items():
        s = sh[k]; s.text_frame.paragraphs[0].runs[0].text = t; s.height = Emu(int(H_HEADER * EMU)); bp = s.text_frame._txBody.find(A + 'bodyPr')
        bp.set('anchor', 'ctr'); bp.set('tIns', '0'); bp.set('bIns', '22860')   # text lifted 0.0125 in: descenders stay on the bar
        ppr = s.text_frame.paragraphs[0]._p.find(A + 'pPr')
        for tag, val in (('lnSpc', '100000'), ('spcBef', '0'), ('spcAft', '0')):
            e_ = ppr.find(A + tag) if ppr is not None else None
            if e_ is not None:
                for g_ in e_:
                    g_.set('val', val)
        for r in s.text_frame.paragraphs[0].runs:
            r.font.size = Pt(HEADER_PT)
        for r in s.text_frame.paragraphs[0].runs[1:]:
            s.text_frame.paragraphs[0]._p.remove(r._r)
    # body / captions
    size = {k: (CAP_PT if k in (4, 13, 30, 36) else BODY_PT) for k in TEXT}
    for k, (lead, body) in TEXT.items():
        set_runs(sh[k], [(lead, True), (body, False)] if lead else [(body, False)], size[k])
    refs = sh[47]; rr = refs.text_frame.paragraphs[0].runs; rr[-1].text = rr[-1].text.rstrip() + REFS_ADD
    for r in rr:
        r.font.size = Pt(REF_PT)
    # Fig. 3
    T = Path(__file__).resolve().parents[1] / 'research/papers/TSI_two_population'   # same figures, re-rendered at 600 dpi from the paper's vector PDFs
    for k, img in ((29, fig3), (3, T / 'fig1_problem_600dpi.png'), (12, T / 'fig2_loop_600dpi.png'), (35, T / 'fig4_mechanism_600dpi.png')):
        old = sh[k]; new = sl.shapes.add_picture(str(img), old.left, old.top, width=old.width); old._element.addprevious(new._element)
        old._element.getparent().remove(old._element); sh[k] = new
    for k in DELETE:
        sh[k]._element.getparent().remove(sh[k]._element)
    # stack the columns
    report = {}; pos = {}
    for c, order in COLS.items():
        x0, w = X[c]; hs = {}
        for k in order:
            s = sh[k]
            if k in HEADERS:
                hs[k] = s.height / EMU
            elif s.shape_type == 13:
                hs[k] = s.height / EMU
            else:
                runs = [(r.text, bool(r.font.bold)) for p in s.text_frame.paragraphs for r in p.runs]; sz = max(r.font.size.pt for p in s.text_frame.paragraphs for r in p.runs)
                ppr = s.text_frame.paragraphs[0]._p.find(A + 'pPr'); ind = int(ppr.get('marL', '0')) / EMU if ppr is not None else 0.0
                hs[k] = heights.get(str(k), text_height(runs, w, sz, ind))
        gaps = []
        for i, k in enumerate(order[:-1]):
            gaps.append(GAP_H if k in HEADERS else GAP_CAP if (sh[k].shape_type == 13 and k in FIGS) else GAP)
        total = sum(hs.values()) + sum(gaps); spare = (BOTTOM - TOP) - total
        figs = [k for k in order if k in FIGS]
        if spare > 0 and figs:                               # spare height grows the figures (to the column width at most), then the gaps
            for k in figs:
                s = sh[k]; ar = s.width / s.height; add = spare / len(figs); nh = min(hs[k] + add, (min(w - 0.02, FIGMAXW.get(k, 99))) / ar); spare -= nh - hs[k]; hs[k] = nh
        if spare < 0 and figs:                               # overfull: shrink the figures, at most to 75 % of their height
            per = -spare / len(figs)
            for k in figs:
                cut = min(per, 0.25 * hs[k]); hs[k] -= cut; spare += cut
        if spare > 0:
            gaps = [g + spare / len(gaps) for g in gaps]
        y = TOP
        for i, k in enumerate(order):
            s = sh[k]
            if s.shape_type == 13:
                ar = s.width / s.height; hh = hs[k]; ww = hh * ar; s.height = Emu(int(hh * EMU)); s.width = Emu(int(ww * EMU)); s.left = Emu(int((x0 + (w - ww) / 2) * EMU))
            else:
                s.left = Emu(int(x0 * EMU)); s.width = Emu(int(w * EMU)); s.height = Emu(int(hs[k] * EMU))
            s.top = Emu(int(y * EMU)); y += hs[k] + (gaps[i] if i < len(gaps) else 0)
        for i, k in enumerate(order):
            pos[str(k)] = dict(col=c, top=sh[k].top / EMU, x0=x0, w=w, text=(k not in HEADERS and sh[k].shape_type != 13),
                               next_top=(sh[order[i + 1]].top / EMU if i + 1 < len(order) else BOTTOM + 0.1))
        report[c] = dict(natural_height=round(total, 3), available=round(BOTTOM - TOP, 3), fill=round(total / (BOTTOM - TOP), 3), bottom=round(y, 3))
    prs.save(out); Path(str(out) + '.pos.json').write_text(json.dumps(pos)); print(json.dumps(report)); return report


def measure_pdf(pdf, posf, outf, pad=0.004):
    """Real height of every text block: from its top to the lowest word rendered between its top and the next block's top."""
    import re, subprocess
    html = subprocess.run(['pdftotext', '-bbox', '-f', '1', '-l', '1', pdf, '-'], capture_output=True, text=True).stdout
    pw = float(re.search(r'<page width="([\d.]+)"', html).group(1)); scale = 10.0 / pw
    W = [tuple(float(x) * scale for x in m.groups()) for m in re.finditer(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)"', html)]
    pos = json.loads(Path(posf).read_text()); H = {}
    for k, p in pos.items():
        if not p['text']:
            continue
        ys = [y1 for x0, y0, x1, y1 in W if x0 >= p['x0'] - 0.01 and x1 <= p['x0'] + p['w'] + 0.01 and y0 >= p['top'] - 0.005 and y1 <= p['next_top'] + 0.005]
        if ys:
            H[k] = max(ys) - p['top'] + pad
    Path(outf).write_text(json.dumps(H, indent=1)); print('measured', len(H), 'text blocks')


if __name__ == '__main__':
    if sys.argv[1] == 'measure':
        measure_pdf(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        hj = json.loads(Path(sys.argv[sys.argv.index('--heights') + 1]).read_text()) if '--heights' in sys.argv else None
        main(sys.argv[1], sys.argv[2], sys.argv[3], hj)
