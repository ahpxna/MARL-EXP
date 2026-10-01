#!/usr/bin/env python3
"""F1 (readiness audit P4): two real traffic decision states, from the target diagnostic (read-only).

State A: the development state whose best single-receiver one-swap gains the most over the prefix in
the continuation label.  State B: a state where no single swap improves (if any), otherwise the state
with the smallest best single-swap gain.  Titles are derived from the data: whether any first action
changes, and the held-phase against continuation gain.
For each: the 3x3 grid of intersections (receivers), the prefix profile P and the continuation-best
SINGLE-RECEIVER ONE-SWAP S*; arrows show, per receiver, the sender added (green) and dropped (red, dashed); a node is
filled when that receiver's first action differs between P and S* (frozen MP2 on the delivered view).
Titles give the held-phase and continuation gains of S* over P.  Source: target_diag_20260928_000455.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

M = Path(__file__).resolve().parents[1] / 'research/marl_budget'


def one_swaps(st):
    P = st['cands'][0]
    return [0] + [k for k, c in enumerate(st['cands'][1:], 1)
                  if sum(len(set(a) - set(b)) for a, b in zip(c['sets'], P['sets'])) == 1]


def draw(ax, st, title):
    P = st['cands'][0]; idx = one_swaps(st)
    g = np.array([st['cands'][k]['cont_3'] - P['cont_3'] for k in idx]); j = idx[int(np.argmax(g))]; S = st['cands'][j]; g = g.max()
    pos = {i: (i % 3, 2 - i // 3) for i in range(9)}
    for i in range(9):
        changed = S['joint'][i] != P['joint'][i]
        ax.scatter(*pos[i], s=900, color='tab:orange' if changed else 'white', edgecolor='k', zorder=3)
        ax.text(*pos[i], f'{i}\nk={st["K"][i]}', ha='center', va='center', fontsize=7, zorder=4)
        add = set(S['sets'][i]) - set(P['sets'][i]); drop = set(P['sets'][i]) - set(S['sets'][i])
        for s_, col, ls in [(a, 'tab:green', '-') for a in add] + [(d, 'tab:red', '--') for d in drop]:
            x0, y0 = pos[s_]; x1, y1 = pos[i]
            ax.annotate('', xy=(x1, y1), xytext=(x0, y0), arrowprops=dict(arrowstyle='->', color=col, ls=ls, lw=1.4,
                        shrinkA=14, shrinkB=14, connectionstyle='arc3,rad=0.15'), zorder=2)
    ax.set_xlim(-0.6, 2.6); ax.set_ylim(-0.6, 2.6); ax.set_aspect('equal'); ax.axis('off')
    ch = [i for i in range(9) if S['joint'][i] != P['joint'][i]]
    how = f'actions change now at {ch}' if ch else 'no action change now; gain later, via caches'
    ax.set_title(f'{title}\n{st["episode"]} t={st["t"]}: {how}\ncontinuation {g:+.0f}, held-phase {S["held_3"] - P["held_3"]:+.0f}', fontsize=8.5)
    return dict(episode=st['episode'], t=st['t'], cont_gain=float(g), held_gain=float(S['held_3'] - P['held_3']),
                changed_receivers=[i for i in range(9) if S['joint'][i] != P['joint'][i]])


def main(a):
    S = json.loads((M / 'target_diag_20260928_000455/rows.json').read_text())
    best = [max(s['cands'][k]['cont_3'] - s['cands'][0]['cont_3'] for k in one_swaps(s)) for s in S]
    A = S[int(np.argmax(best))]; zero = [s for s, b in zip(S, best) if b <= 1e-9]
    Bst = zero[0] if zero else S[int(np.argmin(best))]
    fig, ax = plt.subplots(1, 2, figsize=(10, 5))
    info = [draw(ax[0], A, 'A: the largest single-swap gain'),
            draw(ax[1], Bst, 'B: no single swap improves on the prefix' if zero else 'B: smallest single-swap improvement')]
    fig.text(0.5, 0.02, 'green: sender added for that receiver; red dashed: sender dropped; orange node: its action changes; '
             'k = decoding budget.  Frozen MP2, H = 3, development seeds.', ha='center', fontsize=8)
    od = Path(a.out); od.mkdir(parents=True, exist_ok=True)
    fig.savefig(od / 'fig1_scene.png', dpi=200, bbox_inches='tight'); fig.savefig(od / 'fig1_scene.pdf', bbox_inches='tight'); plt.close(fig)
    (od / 'fig1_scene.json').write_text(json.dumps(dict(states=info, n_states_no_improvement=len(zero)), indent=1)); print(json.dumps(info))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--out', default=str(M / 'figures_20260928_v4')); main(p.parse_args())
