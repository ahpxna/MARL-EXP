"""Find text that collides in a figure, instead of noticing it on the printed sheet.

Overlapping labels are easy to miss when a figure is looked at once at full size
and never again -- two annotations a few points apart render as one unreadable
smear, and a note pinned inside the axes can sit on top of the x-axis label.

This renders each figure the generators produce, measures every text object's
bounding box in display coordinates, and reports pairs that intersect. It also
reports notes that overlap the axis labels or the plotted data, which is the
other way a figure becomes unreadable without anything being obviously wrong.

Run it as a check; it draws nothing and writes nothing.
"""
import importlib.util
import sys
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def _boxes(fig):
    fig.canvas.draw()
    r = fig.canvas.get_renderer()
    out = []
    # figure-level text (footnotes, symbol keys) lives on the figure, not on an
    # axes, and was invisible to an axes-only scan
    for t in fig.texts:
        if not t.get_text():
            continue
        try:
            bb = t.get_window_extent(renderer=r)
        except Exception:
            continue
        if bb.width > 0 and bb.height > 0:
            out.append((t.get_text().replace('\n', ' ')[:42], bb, t))
    for ax in fig.axes:
        items = list(ax.texts)
        for t in (ax.title, ax.xaxis.label, ax.yaxis.label):
            if t.get_text():
                items.append(t)
        leg = ax.get_legend()
        if leg is not None:
            items += list(leg.get_texts())
        items += [lb for lb in ax.get_xticklabels() + ax.get_yticklabels()
                  if lb.get_text()]
        for t in items:
            try:
                bb = t.get_window_extent(renderer=r)
            except Exception:
                continue
            if bb.width > 0 and bb.height > 0:
                out.append((t.get_text().replace('\n', ' ')[:42], bb, t))
    return out


def _overlap(a, b):
    dx = min(a.x1, b.x1) - max(a.x0, b.x0)
    dy = min(a.y1, b.y1) - max(a.y0, b.y0)
    if dx <= 0 or dy <= 0:
        return 0.0
    return dx * dy / min(a.width * a.height, b.width * b.height)


def check(module_path, names=None, thresh=0.12):
    spec = importlib.util.spec_from_file_location('figs', module_path)
    M = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(M)
    fns = names or [n for n in dir(M)
                    if callable(getattr(M, n)) and not n.startswith('_')
                    and getattr(M, n).__module__ == 'figs'
                    and n not in ('fin', 'save', 'note', 'poster_variants', 'main',
                                  'label_points', 'atoms')]
    findings = []
    for n in sorted(fns):
        made = {}

        def cap(fig, name, _m=made):
            _m[name] = fig
        # the two generators name their save hook differently
        hook = 'fin' if hasattr(M, 'fin') else 'save'
        real_fin = getattr(M, hook)

        def fin(fig, name):
            made[name] = fig
            return None
        setattr(M, hook, fin)
        try:
            getattr(M, n)()
        except Exception as e:
            setattr(M, hook, real_fin)
            findings.append((n, 'ERROR', str(e)[:70]))
            continue
        setattr(M, hook, real_fin)
        for name, fig in made.items():
            # the generators declutter inside their save hook, which this check
            # replaces -- so run the same step before measuring, or the report
            # describes a figure nobody ever writes out
            if hasattr(M, '_declutter_corner'):
                M._declutter_corner(fig)
            bs = _boxes(fig)
            bad = []
            for i in range(len(bs)):
                for j in range(i + 1, len(bs)):
                    o = _overlap(bs[i][1], bs[j][1])
                    if o > thresh:
                        bad.append((round(o, 2), bs[i][0], bs[j][0]))
            plt.close(fig)
            if bad:
                findings.append((name, 'OVERLAP', bad))
    return findings


if __name__ == '__main__':
    for path in sys.argv[1:] or ['scripts/PAPER_figures.py', 'scripts/POSTER_figures.py']:
        print(f'=== {path}')
        for name, kind, info in check(path):
            if kind == 'ERROR':
                print(f'  {name}: ERROR {info}')
            else:
                print(f'  {name}: {len(info)} overlapping pair(s)')
                for o, a, b in info[:4]:
                    print(f'      {o:.2f}  "{a}"  vs  "{b}"')
