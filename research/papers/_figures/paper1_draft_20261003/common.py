"""Shared helpers for the paper-1 figure drafts (read-only on the repo).  Palette: the dataviz skill's validated reference
categorical slots 1-3 (blue #2a78d6, orange #eb6834, aqua #1baf7a; all-pairs CVD dE >= 9.2, light mode) + its diverging
blue<->red pair with a gray midpoint.  Aqua sits below 3:1 contrast -> always direct-labelled."""
import json, hashlib, os
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap

ROOT = Path('/Users/phanan/cig-amf-main'); MB = ROOT / 'research/marl_budget'
OUT = Path(__file__).parent
BLUE, ORANGE, AQUA = '#2a78d6', '#eb6834', '#1baf7a'
INK, INK2, MUTED, GRID, SURF = '#0b0b0b', '#52514e', '#8a8984', '#e6e5e1', '#fcfcfb'
DIVERGING = LinearSegmentedColormap.from_list('redgraybl', ['#a32c2b', '#e34948', '#f3b7b0', '#f0efec', '#9ec5f4', '#2a78d6', '#184f95'])
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9, 'axes.edgecolor': MUTED, 'axes.labelcolor': INK, 'text.color': INK,
                     'xtick.color': INK2, 'ytick.color': INK2, 'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.grid': True, 'grid.color': GRID, 'grid.linewidth': 0.6, 'axes.axisbelow': True,
                     'figure.facecolor': SURF, 'axes.facecolor': SURF, 'savefig.facecolor': SURF, 'pdf.fonttype': 42, 'legend.frameon': False})

def save(fig, name):
    for ext in ('png', 'pdf'):
        fig.savefig(OUT / f'{name}.{ext}', dpi=200 if ext == 'png' else None, bbox_inches='tight')
    plt.close(fig)

def sha_file(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def gain(x, z, ii=None):
    return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100

def boot2(pairs, B=2000, seed=0):
    """two-level bootstrap (seeds, then traffic seeds shared within a draw) of the mean of gain(X, Z); pairs = [(X, Z)] per seed,
    episodes ordered (traffic seed t, headway 8 / 16) so traffic seed k -> indices 2k, 2k+1."""
    rng = np.random.default_rng(seed); n = len(pairs); out = []
    for _ in range(B):
        ss = rng.integers(0, n, n); tt = rng.integers(0, 64, 64); ii = np.concatenate([2 * tt, 2 * tt + 1])
        out.append(np.mean([gain(pairs[i][0], pairs[i][1], ii) for i in ss]))
    return [float(v) for v in np.percentile(out, [2.5, 97.5])]

def seed_boot(v, B=20000, rng=None):
    rng = rng or np.random.default_rng(0); v = np.asarray(v, float)
    return [float(x) for x in np.percentile(v[rng.integers(0, len(v), (B, len(v)))].mean(1), [2.5, 97.5])]

def episodes(t0):
    return [f'seed{s}_load{h}' for s in range(t0, t0 + 64) for h in (8, 16)]

def load_rows(d, field, value, eps):
    r = {x['episode']: x['queue_sum'] for x in json.loads((Path(d) / 'rows.json').read_text()) if x.get(field) == value}
    assert set(eps) <= set(r), (d, value, len(r))
    return np.array([r[e] for e in eps], float)

def manifest(d):
    m = json.loads((Path(d) / 'manifest.json').read_text()); assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', d
    return m
