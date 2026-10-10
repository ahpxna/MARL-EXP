#!/usr/bin/env python3
"""Poster Fig. 2 for the TSI poster: the closed loop as one flat row (the paper's p1 schematic, re-drawn compactly).
Traffic -> sensing -> input map g -> learned signal -> timing -> SPaT provider P -> learned fleet -> approach -> traffic.
The two interfaces TSI changes are outlined in blue; the two frozen policies are grey; the self-defeating path is orange.
Usage: POSTER_tsi_fig2.py <out stem>     (writes <stem>.png / .pdf; refuses to overwrite)"""
import sys
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Rectangle, FancyArrowPatch  # noqa: E402
BLUE, ORANGE, GRAY, LGRAY, INK, INK2 = '#2a78d6', '#eb6834', '#8a8984', '#d6d5cf', '#0b0b0b', '#52514e'
plt.rcParams.update({'font.size': 8, 'text.color': INK, 'pdf.fonttype': 42, 'font.family': 'DejaVu Sans', 'mathtext.fontset': 'dejavusans'})


def main(stem):
    out = Path(stem)
    if out.with_suffix('.png').exists() or out.with_suffix('.pdf').exists():
        raise SystemExit(f'refusing to overwrite {out}')
    fig, ax = plt.subplots(figsize=(7.2, 1.75)); ax.set_xlim(0, 14.4); ax.set_ylim(0, 3.5); ax.axis('off')
    Y, H, W = 2.05, 1.25, 2.42
    xs = [0.1 + k * 2.93 for k in range(5)]
    nodes = [('Traffic', 'queues, speeds', None), ('Input map $g$', 'what the signal sees', 'tsi'),
             ('Signal $\\pi_L$', 'learned, frozen', 'frozen'), ('SPaT $P$', 'what the fleet is told', 'tsi'),
             ('Fleet $\\pi_F$', 'learned, frozen', 'frozen')]
    for x, (t, s, kind) in zip(xs, nodes):
        fc = '#f1f0ec' if kind == 'frozen' else 'white'; ec = BLUE if kind == 'tsi' else GRAY; lw = 1.6 if kind == 'tsi' else 0.8
        ax.add_patch(Rectangle((x, Y), W, H, fc=fc, ec=ec, lw=lw))
        ax.text(x + W / 2, Y + H * 0.66, t, ha='center', va='center', fontsize=8.4, fontweight='bold')
        ax.text(x + W / 2, Y + H * 0.28, s, ha='center', va='center', fontsize=6.3, color=INK2)

    def arrow(p0, p1, col=INK2, lw=0.9, rad=0.0):
        ax.add_patch(FancyArrowPatch(p0, p1, arrowstyle='-|>', mutation_scale=8, lw=lw, color=col, connectionstyle=f'arc3,rad={rad}'))
    ym = Y + H / 2
    for a, b in zip(xs[:-1], xs[1:]):
        arrow((a + W + 0.04, ym), (b - 0.04, ym))
    # TSI annotations under the two blue boxes
    ax.text(xs[1] + W / 2, Y - 0.22, '$q = h + A\\,n_{0.1\\text{–}2} + B\\,n_{2\\text{–}5}$\n(halted + slow + mid-speed)', ha='center', va='top', fontsize=6.9, color=BLUE, linespacing=1.35)
    ax.text(xs[3] + W / 2, Y - 0.22, 'exact in a determined yellow,\nquantile forecast otherwise', ha='center', va='top', fontsize=6.9, color=BLUE, linespacing=1.35)
    # the closed loop: the fleet's reaction re-enters traffic
    yb = 0.32
    ax.plot([xs[4] + W / 2, xs[4] + W / 2], [Y, yb], color=ORANGE, lw=1.2)
    ax.plot([xs[4] + W / 2, xs[0] + W / 2], [yb, yb], color=ORANGE, lw=1.2)
    arrow((xs[0] + W / 2, yb), (xs[0] + W / 2, Y), col=ORANGE, lw=1.2)
    ax.text((xs[2] + W / 2), yb + 0.1, 'gliding agents leave the halting count $\\rightarrow$ longer greens $\\rightarrow$ the forecast misses its own target',
            ha='center', va='bottom', fontsize=6.9, color=ORANGE, style='italic')
    for ext in ('png', 'pdf'):
        fig.savefig(out.with_suffix('.' + ext), dpi=300, bbox_inches='tight', pad_inches=0.03)
    print('wrote', out)


if __name__ == '__main__':
    main(sys.argv[1])
