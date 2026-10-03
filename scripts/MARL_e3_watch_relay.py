#!/usr/bin/env python3
"""Watch RELAY-student episodes in CityFlow's replay viewer (02/10/2026 01:2x EDT; user 01:1x "visualize the traffic flow").
Read-only tool, not an experiment: one episode per run, recorded with CityFlow's replay switched on in a COPY of the
scenario config, then a viewer directory with CityFlow's frontend and autoload.js (scripts/MARL_e3_watch_episode.py's).
Runs (--run name:mode:K): mode z = the zero-byte student on its local view (compiled silence); mode relay = the relay
student under age-first, relay v2 merge, 3 B codebook, constant K (K = 0: the iid capacity process).  Use through
scripts/MARL_grid_relay_wrapper.py for the 4×4 grid.  SELF-CHECK (--parity name=rows.json): the episode's queue sum must
equal the evaluated row (e.g. the 4×4 development look), so the replay shows exactly the evaluated episode.
"""
from __future__ import annotations
import argparse, copy, json, shutil, sys
from dataclasses import replace
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import scenario, new_env
from scripts.MARL_e3_zero_loss_truncation import make
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery
from scripts.MARL_e3_negflip_probe import ZPol
from scripts.MARL_e3_watch_episode import AUTOLOAD, FRONTEND
FIT = r'''
// fit the whole network in the VISIBLE canvas area (MARL_e3_watch_relay.py, 02/10 01:3x) + buttons "Xem toàn bộ" / chart toggle;
// refits whenever the viewer recreates its viewport (drawRoadnet).  Wheel = zoom, drag = pan.
function fitNetwork() {
  const cv = document.getElementById('simulator-canvas').getBoundingClientRect(); const ch = document.getElementById('chart-container');
  const chartTop = (ch && ch.style.display !== 'none') ? ch.getBoundingClientRect().top : cv.bottom;
  const Wv = cv.width, Hv = Math.max(200, chartTop - cv.top); const b = simulatorContainer.getLocalBounds();
  const cx = simulatorContainer.x + b.x + b.width / 2, cy = simulatorContainer.y + b.y + b.height / 2;
  const s = 0.94 * Math.min(Wv / b.width, Hv / b.height); viewport.scale.set(s); viewport.position.set(Wv / 2 - s * cx, Hv / 2 - s * cy);
}
(function fitLoop(k) {
  try {
    if (typeof simulatorContainer !== 'undefined' && simulatorContainer && simulatorContainer.children.length >= 3 &&
        typeof viewport !== 'undefined' && viewport && !viewport.__fitted) { fitNetwork(); viewport.__fitted = true; }
  } catch (e) { console.warn('fit failed', e); }
  if (k < 120) setTimeout(() => fitLoop(k + 1), 500);
})(0);
(function buttons() {
  const bar = document.createElement('div'); bar.style = 'position:fixed;top:26px;right:8px;z-index:9;font:13px sans-serif;display:flex;gap:6px';
  const mk = (t, f) => { const x = document.createElement('button'); x.textContent = t; x.onclick = f; x.style = 'padding:3px 8px;cursor:pointer'; bar.appendChild(x); };
  mk('Xem toàn bộ', () => { try { fitNetwork(); } catch (e) {} });
  mk('Ẩn/hiện biểu đồ', () => { const ch = document.getElementById('chart-container'); if (ch) ch.style.display = ch.style.display === 'none' ? '' : 'none'; try { fitNetwork(); } catch (e) {} });
  document.body.appendChild(bar);
})();
'''


class ReplayScenarios:
    def __init__(self, out, name):
        self.out = out; self.name = name; self.cache = {}

    def env(self, seed, load):
        if (seed, load) not in self.cache:
            self.cache[(seed, load)] = scenario(self.out, seed, load)
        s = copy.deepcopy(self.cache[(seed, load)]); d = Path(s['dir']); cfg = json.loads(Path(s['files']['config.json']['path']).read_text())
        cfg.update(saveReplay=True, roadnetLogFile=f'replay_{self.name}_roadnet.json', replayLogFile=f'replay_{self.name}.txt')
        rc = d / f'config_replay_{self.name}.json'; rc.write_text(json.dumps(cfg)); s['files']['config.json']['path'] = str(rc)
        self.dir = d
        return new_env(s, seed, load)


def local_only(v):
    return replace(v, inbox=(), cache=(), never_heard=tuple(sorted(int(j) for j in v.neighbours)))


def episode(sc, seed, load, mode, K, ck, ckz, book):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4) if mode == 'relay' else CommAdapter
    env, pol = make(sc, seed, load, ck if mode == 'relay' else ckz, 'iid')
    zpol = ZPol(ckz, pol.adapter.topos, pol.adapter.interval) if mode == 'z' else None
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            if mode == 'z':
                a = zpol.act_views([local_only(mv[i]) for i in range(m)])
            else:
                X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
                with torch.no_grad():
                    a = pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1)
            _, _, rec = env.step({i: int(a[i]) for i in range(m)})
        q.append(float(rec['queue']))
    del env
    return q


def main(a):
    out = Path(a.out); v = out / 'viewer'; v.mkdir(parents=True, exist_ok=True)
    book = json.loads((ROOT / a.codebook).read_text())
    ck = torch.load(a.relay, weights_only=False); ckz = torch.load(a.z, weights_only=False)
    par = {}
    for spec in a.parity:
        n, _, f = spec.partition('=')
        par[n] = {r['episode']: r['queue_sum'] for r in json.loads(Path(f).read_text()) if r.get('rule') in (None, 'prefix', 'none')}
    runs_f = out / 'runs.json'; runs = json.loads(runs_f.read_text()) if runs_f.exists() else {}
    ep = f'seed{a.seed}_load{a.headway:g}'
    for spec in a.run:
        name, mode, K = spec.split(':'); K = int(K)
        sc = ReplayScenarios(out / f'work_{name}', name); q = episode(sc, a.seed, a.headway, mode, K, ck, ckz, book)
        if name in par:
            if ep not in par[name] or abs(par[name][ep] - sum(q)) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {name} {ep} waiting {sum(q)} != evaluated row {par[name].get(ep)}')
            print(f'{name}: parity with the evaluated row PASS', flush=True)
        od = v / name; od.mkdir(exist_ok=True)
        shutil.copy(sc.dir / f'replay_{name}_roadnet.json', od / 'replay_roadnet.json'); shutil.copy(sc.dir / f'replay_{name}.txt', od / 'replay.txt')
        runs[name] = dict(q=q, mode=mode, K=K, parity=name in par); print(f'{name}: Σ waiting {sum(q):.0f}', flush=True)
    runs_f.write_text(json.dumps(runs))
    names = list(runs)
    for name in names:                                            # chart: waiting per decision step, one column per run
        L = sum(1 for _ in open(v / name / 'replay.txt')); per = max(1, L // N_DEC)
        rows_ = [' '.join(f'{runs[n]["q"][min(s // per, N_DEC - 1)]:.0f}' for n in names) for s in range(L)]
        (v / name / 'chart.txt').write_text('waiting vehicles (' + ' / '.join(names) + ')\n' + '\n'.join(rows_) + '\n')
    for f in ('index.html', 'script.js', 'Point.js', 'style.css', 'spinner.css'):
        shutil.copy(FRONTEND / f, v / f)
    (v / 'autoload.js').write_text(f'const RUNS = {json.dumps(names)};\n' + AUTOLOAD + FIT)
    html = (v / 'index.html').read_text()
    if 'autoload.js' not in html:
        (v / 'index.html').write_text(html.replace('</body>', '<script src="autoload.js"></script>\n</body>'))
    (out / 'watch.json').write_text(json.dumps(dict(seed=a.seed, headway=a.headway, relay=a.relay, z=a.z,
                                                    waiting_sum={n: sum(r['q']) for n, r in runs.items()}), indent=1))
    print('viewer ready:', v, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--z', required=True)
    p.add_argument('--run', action='append', required=True, help='name:mode:K, mode z or relay, K = 0 for iid')
    p.add_argument('--parity', action='append', default=[], help='name=rows.json of the evaluated episode')
    p.add_argument('--seed', type=int, default=901); p.add_argument('--headway', type=float, default=8.0)
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--out', required=True)
    main(p.parse_args())
