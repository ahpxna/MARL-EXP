#!/usr/bin/env python3
"""Builds demo/gridlock_to_green.html: demo/page_template.html with the recorded test scenes (demo/data/{today,best,broken,fixed}.json from
DEMO_record.py), the training replays (demo/data/train_{light,fleet}.json from DEMO_record_train.py, if present), their learning curves (the
B2D light t59 training log; the FRESH3 fleet s1413 training output; 10-episode moving average) and the grid4 geometry inlined, so the page runs
offline (open the file in a browser) and as an artifact."""
import json, re
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; D = ROOT / 'demo'
data = dict(net=json.loads((D / 'data/net.json').read_text()), scenes={k: json.loads((D / f'data/{k}.json').read_text()) for k in ('today', 'best', 'broken', 'fixed')})


def smooth(y, k=10):
    y = np.asarray(y, float); return [round(float(np.mean(y[max(0, i - k + 1):i + 1])), 4) for i in range(len(y))]


if (D / 'data/train_light.json').exists() and (D / 'data/train_fleet.json').exists():
    lt = json.loads((D / 'data/train_light.json').read_text()); fl = json.loads((D / 'data/train_fleet.json').read_text())
    lc = [r['mean_r'] for r in json.loads((ROOT / 'research/city_sim/w19_20261008/lights/RL-H_t59.log.json').read_text())]
    fc = [float(m.group(1)) for m in re.finditer(r' ep \d+ .*?meanR (-?[\d.]+)', (ROOT / 'research/city_sim/w15_20261007/fresh3/fleets/L11_s1413.out').read_text())]
    data['train'] = dict(light=dict(episodes=lt['episodes'], tls=lt['tls'], n=len(lc), curve=smooth(lc), label='light reward per decision, rising = less delay'),
                         fleet=dict(episodes=fl['episodes'], tls=fl['tls'], n=len(fc), curve=smooth(fc), label='car reward per decision, rising = less fuel'))
blob = json.dumps(data, separators=(',', ':')).replace('</', '<\\/')
html = (D / 'page_template.html').read_text().replace('__DATA__', blob)
(D / 'gridlock_to_green.html').write_text(html); print('wrote', D / 'gridlock_to_green.html', round(len(html) / 2 ** 20, 2), 'MB', 'with training replay' if 'train' in data else 'without training replay')
