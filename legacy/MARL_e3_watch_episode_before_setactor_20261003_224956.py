#!/usr/bin/env python3
"""Watch a CityFlow episode in the browser: record replays and open CityFlow's own replay viewer (read-only tool).

CityFlow has no live window.  Its viewer (external_envs/repos/CityFlow/frontend) replays a roadnet log + replay file.
This tool runs ONE episode per method with the deployed protocol (committed cached-queue prefix, R = 0, every scheduler
call inside no_oracle_access, access invariants every step), with CityFlow's replay switched on in a COPY of the
scenario config (the pinned scenario and the running experiments are untouched), then builds a viewer directory:
  <out>/viewer/                  copy of the CityFlow frontend + autoload.js (fetches the files and presses Start)
  <out>/viewer/<method>/         replay_roadnet.json, replay.txt, chart.txt (Σ waiting per second of every method)
Open http://localhost:<port>/?run=<method> after `python3 -m http.server <port> --directory <out>/viewer`.
Methods: actor=<ckpt> (a frozen learned actor; e.g. a RUNNING training's ckpt_best.pt, read-only) and/or mp2.
Refuses the reserved test seeds 1301-1316.  Nothing here is an experiment result.
"""
from __future__ import annotations
import argparse, copy, json, shutil, sys
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import scenario, new_env, grant
from scripts.MARL_e3_continuation_labels import Policy

FRONTEND = ROOT / 'external_envs/repos/CityFlow/frontend'
TEST_SEEDS = set(range(1301, 1317))
AUTOLOAD = r'''// autoload.js (MARL_e3_watch_episode.py): fetch the run's files, put them in the upload inputs, press Start.
(async function () {
  const run = new URLSearchParams(location.search).get('run') || RUNS[0];
  const put = async (id, url, name) => {
    const r = await fetch(url); if (!r.ok) return false;
    const dt = new DataTransfer(); dt.items.add(new File([await r.blob()], name));
    const el = document.getElementById(id); el.files = dt.files; el.dispatchEvent(new Event('change')); return true;
  };
  await put('roadnet-file', run + '/replay_roadnet.json', 'replay_roadnet.json');
  await put('replay-file', run + '/replay.txt', 'replay.txt');
  await put('chart-file', run + '/chart.txt', 'chart.txt');
  const nav = document.createElement('div'); nav.style = 'position:fixed;top:4px;right:8px;z-index:9;font:13px sans-serif';
  nav.innerHTML = 'run: ' + RUNS.map(x => x === run ? '<b>' + x + '</b>' : '<a href="?run=' + x + '">' + x + '</a>').join(' | ');
  document.body.appendChild(nav);
  document.getElementById('start-btn').click();
  // legend: Chartist colours its series a, b, c, ... in this order (chartist.min.css defaults); CityFlow's page has none
  const COLORS = ['#d70206', '#f05b4f', '#f4c63d', '#d17905', '#453d3f', '#59922b', '#0544d3', '#6b0392', '#f05b4f', '#dda458'];
  const legend = 'waiting vehicles per second (one line per run; the cars shown are <b>' + run + '</b>): ' +
    RUNS.map((x, i) => '<span style="color:' + COLORS[i % COLORS.length] + ';font-weight:600;white-space:nowrap">&#9632; ' + x + '</span>').join(' &nbsp; ');
  const fix = () => { const t = document.getElementById('chart-title'); if (t && !t.innerHTML.includes('&#9632;') && !t.innerHTML.includes('■')) t.innerHTML = legend; };
  for (let k = 1; k <= 20; k++) setTimeout(fix, 500 * k);
})();
'''


def run_episode(scen, seed, load, method, ck, out):
    s = copy.deepcopy(scen); d = Path(s['dir']); cfg = json.loads(Path(s['files']['config.json']['path']).read_text())
    cfg.update(saveReplay=True, roadnetLogFile=f'replay_{method}_roadnet.json', replayLogFile=f'replay_{method}.txt')
    rc = d / f'config_replay_{method}.json'; rc.write_text(json.dumps(cfg)); s['files']['config.json']['path'] = str(rc)
    env, topo, down, onward = new_env(s, seed, load); m = env.n_agents
    pol = Policy(ck, topo, env.action_interval) if ck is not None else None; q = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            order, K = grant(env); env.submit_profile(prefix_sets(order, K), R=0)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()} if pol is None else pol.act(views)
            _, _, rec = env.step(acts)
        q.append(float(rec['queue']))
    del env
    od = out / 'viewer' / method; od.mkdir(parents=True, exist_ok=True)
    shutil.copy(d / f'replay_{method}_roadnet.json', od / 'replay_roadnet.json'); shutil.copy(d / f'replay_{method}.txt', od / 'replay.txt')
    return q


def main(a):
    if a.seed in TEST_SEEDS:
        raise SystemExit('refusing: 1301-1316 are reserved for the frozen confirmatory test')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    scen = scenario(out, a.seed, a.headway); runs = {}
    for spec in a.method:
        name, _, path = spec.partition('=')
        ck = torch.load(path, weights_only=False) if path else None
        if name != 'mp2' and ck is None:
            raise SystemExit(f'{spec}: give actor=<ckpt path>')
        runs[name] = run_episode(scen, a.seed, a.headway, name, ck, out)
        print(f'{name}: Σ waiting {sum(runs[name]):.0f} over {N_DEC} decisions', flush=True)
    names = list(runs)
    for name in names:                                            # chart: one line per replay step, one column per method
        L = sum(1 for _ in open(out / 'viewer' / name / 'replay.txt')); per = max(1, L // N_DEC)
        rows = [' '.join(f'{runs[n][min(s // per, N_DEC - 1)]:.0f}' for n in names) for s in range(L)]
        (out / 'viewer' / name / 'chart.txt').write_text('waiting vehicles (' + ' / '.join(names) + ')\n' + '\n'.join(rows) + '\n')
    v = out / 'viewer'
    for f in ('index.html', 'script.js', 'Point.js', 'style.css', 'spinner.css'):
        shutil.copy(FRONTEND / f, v / f)
    (v / 'autoload.js').write_text(f'const RUNS = {json.dumps(names)};\n' + AUTOLOAD)
    html = (v / 'index.html').read_text()
    if 'autoload.js' not in html:
        (v / 'index.html').write_text(html.replace('</body>', '<script src="autoload.js"></script>\n</body>'))
    (out / 'watch.json').write_text(json.dumps(dict(seed=a.seed, headway=a.headway, methods=a.method, waiting_sum={n: sum(q) for n, q in runs.items()}), indent=1))
    print(f'viewer: python3 -m http.server {a.port} --directory {v}   then open http://localhost:{a.port}/?run={names[0]}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--method', action='append', required=True, help='actor=<ckpt path> (any name) or mp2')
    p.add_argument('--seed', type=int, default=501); p.add_argument('--headway', type=float, default=8.0)
    p.add_argument('--out', required=True); p.add_argument('--port', type=int, default=8765)
    main(p.parse_args())
