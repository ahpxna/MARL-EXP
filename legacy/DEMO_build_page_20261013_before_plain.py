#!/usr/bin/env python3
"""Builds demo/gridlock_to_green.html ("When AIs meet AIs") from demo/page_template.html with every number and recording inlined, so the
page runs offline and as an artifact.  Rebuilt 11/10/2026 after the demo review (research/catchup/DEMO_MIDTOWN_REVIEW_20261011.md):
every comparison has its own cards, source and denominator; generated signal plans are not called "Today"; human-only runs are drawn
without AI colour; "time stopped" instead of "stopped at red"; MPLight is "DQN with RESCO MPLight's state/reward representation".
Views
  mt    Midtown Manhattan, FULL map (Overpass 11/10: 567 signals, 206 km; PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010 MT-C/E): AI on the 511 two-green
        signals and the city's actuated programs on the 56 complex ones (MT_BASE=actrest).  Cards: test days 0-4, eval_full/MTF_LGar_t* (5 grid lights)
        and MTF_BGar_t*_s* (5 lights x 4 grid fleets) against MTF_ACT / MTF_FT on every signal.  Clip: test day 0 = the median day of the actuated
        baseline's delay (same rule as before), light t59, fleet s1413, minutes 25-30.  (The old partial map's view: legacy/DEMO_build_page_oldmidtown_20261011.py.)
  ai2   Two AIs (grid, W20 panel research/city_sim/w20_20261009/report_w20.txt: 20 traffic days x 5 lights x 4 fleets): the same learned
        light and the same AI fleet with the forecast service, without vs with TSI-G.  sumo-rl state (k84, repair gate passed) and RESCO
        MPLight state (k94, large partial repair, final gate missed).  Clips: seed 1400, minutes 25-30.
  grid  The 16-signal test grid: fixed-time vs AI lights + AI fleet (panel numbers as before).
Training replays (demo/data/train_{light,fleet}.json) play in the corner window on request."""
import json, re
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; D = ROOT / 'demo'; E5 = ROOT / 'research/city_sim/midtown_transfer_20261010/eval_full'   # full map (MT-C/E)
J = lambda p: json.loads(Path(p).read_text())


def smooth(y, k=10):
    y = np.asarray(y, float); return [round(float(np.mean(y[max(0, i - k + 1):i + 1])), 4) for i in range(len(y))]


def pct(a, b):
    return f'−{round(100 * (a - b) / a)}%' if b < a else f'+{round(100 * (b - a) / a)}%'


def rows(tag):
    d = J(E5 / f'{tag}.json'); assert d['status'] == 'COMPLETE', tag; r = {x['seed']: x for x in d['rows']}; assert sorted(r) == [0, 1, 2, 3, 4], tag; return r


def scene(key, coarse=False, **meta):
    s = J(D / f'data/{key}.json'); s.update(meta); s['posScale'] = 10
    if coarse:                                                      # Midtown: positions to 1 m (the map is drawn at ~0.2 px per m), 2 s frames
        keep_ai = not meta.get('allHuman')                          # the renderer reads v[4] only as "stopped (< 1)" and v[5] only for AI runs
        for f in s['frames']:
            f['v'] = [[v[0], round(v[1] / 10), round(v[2] / 10), v[3], int(v[4] >= 1)] + (v[5:6] if keep_ai else []) for v in f['v']]
        s['frames'] = s['frames'][::2]; s['dt'] = 2                   # 2 s per stored frame; the renderer interpolates (page < 16 MB)
        s['posScale'] = 1
    return s


def busiest_box(net, keys, size, step=25.0):
    """the size x size window with the most vehicle-seconds, both clips of the default comparison summed (zoom rule, fixed in advance)"""
    pts = np.array([[v[1] / 10, v[2] / 10] for k in keys for f in J(D / f'data/{k}.json')['frames'] for v in f['v']])
    x0, y0, x1, y1 = net['bbox']; best = None
    for cx in np.arange(x0, x1 - size + 1e-9, step):
        for cy in np.arange(y0, y1 - size + 1e-9, step):
            n = int(((pts[:, 0] >= cx) & (pts[:, 0] < cx + size) & (pts[:, 1] >= cy) & (pts[:, 1] < cy + size)).sum())
            if best is None or n > best[0]:
                best = (n, [round(cx, 1), round(cy, 1), round(cx + size, 1), round(cy + size, 1)])
    return best[1]


nets = dict(grid=J(D / 'data/net.json'), mt=J(D / 'data/net_midtown_full.json'))
# ---------------------------------------------------------------- Midtown, FULL map (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010 MT-C/E): AI on the 511 two-green
# signals, the city's actuated programs on the 56 complex ones (MT_BASE=actrest); baselines FT / ACT on every signal
ft, act = rows('MTF_FT'), rows('MTF_ACT'); LG = [rows(f'MTF_LGar_t{k}') for k in range(59, 64)]; days = range(5)
BG = [rows(f'MTF_BGar_t{k}_s{f}') for k in range(59, 64) for f in (1413, 1513, 1613, 1713)]   # grid lights x grid fleets, adapted forecast
m1 = lambda R, k: float(np.mean([R[d][k] for d in days]))
mG = lambda G, k: float(np.mean([[r[d][k] for d in days] for r in G]))
mL = lambda k: mG(LG, k)
tel = lambda Rs: float(np.mean([r[d]['teleports'] for r in Rs for d in days]))


def mt_cards(B, G=None, B_is_group=False):
    G = G or LG; b = (lambda k: mG(B, k)) if B_is_group else (lambda k: m1(B, k))
    tl0, tl1, w0, w1, f0, f1 = b('timeloss'), mG(G, 'timeloss'), b('waiting'), mG(G, 'waiting'), b('fuel') / 1000, mG(G, 'fuel') / 1000
    return [dict(big=pct(tl0, tl1), what='delay per trip', **{'from': f'{tl0:.0f} → {tl1:.0f} seconds'}),
            dict(big=pct(w0, w1), what='time stopped per trip', **{'from': f'{w0:.0f} → {w1:.0f} seconds'}),
            dict(big=pct(f0, f1), what='fuel per trip', **{'from': f'{f0:.0f} → {f1:.0f} grams'})]


_map = ('SUMO simulation of the full OpenStreetMap extract of Midtown Manhattan (about 19th–74th Street, river to river: 567 signals, 206 km of road); '
        '4 800 random trips an hour for one hour. The AI runs the 511 two-phase intersections; the 56 complex junctions run the city\'s actuated programs, as in the baseline. ')
mt_foot = (_map + 'All cars human-driven (SUMO model). Cards: means over 5 test days × 5 independently trained signal models (25 runs), learned on a 16-signal grid '
           f'and transferred without weight retraining. Cars removed by SUMO after 300 s stuck, per run: {{base}} {{bt:.1f}}, AI {tel(LG):.1f}. '
           'Clip: test day 0 (the median day of the actuated baseline), model t59, minutes 25–30. Simulation baselines, not NYC\'s live signal system (Midtown in Motion).')
mt_foot_best = (_map + 'Half the cars are the AI eco-driving fleet, which receives a forecast of each AI signal. Cards: means over 5 test days × 5 signal models × 4 fleets '
                '(100 runs), all learned on a 16-signal grid and transferred without weight retraining; paired with actuated on the same day, delay was lower in 98 of 100 runs. '
                f'Cars removed by SUMO after 300 s stuck, per run: {{base}} {{bt:.1f}}, AI {tel(BG):.1f}. Clip: test day 0 (the median day of the actuated baseline), '
                'signal model t59 with fleet s1413, minutes 25–30. Simulation baselines, not NYC\'s live signal system (Midtown in Motion).')
scenes = dict(
    mtf0_best=scene('mtf0_best', coarse=True, tag='AI + AI', tagClass='ai', title='AI signals + AI cars, both learned on a 16-signal grid', delay=BG[0][0]['timeloss'],
                    caption='Same streets and day. Half the cars are AI: they know when each AI signal will turn and glide in instead of stopping.'),
    mtf0_act=scene('mtf0_act', coarse=True, tag='Baseline', tagClass='base', title='Actuated signals (SUMO simulation baseline)', allHuman=True, delay=act[0]['timeloss'],
                   caption='Each signal holds green while its detectors see cars: a reactive controller, run on the same streets and the same traffic.'),
    mtf0_ft=scene('mtf0_ft', coarse=True, tag='Baseline', tagClass='base', title='Fixed-time signals (SUMO-generated plan)', allHuman=True, delay=ft[0]['timeloss'],
                  caption='90-second cycles generated by SUMO from the map data, not the city\'s timing plans. On the full map they gridlock.'),
    mtf0_light=scene('mtf0_light', coarse=True, tag='AI', tagClass='ai', title='AI signals, learned on a 16-signal grid', allHuman=True, delay=LG[0][0]['timeloss'],
                     caption='Same streets, same cars, same day. Every 5 s each AI signal decides to keep or switch, from how far away the waiting cars are.'),
    broken_srl=scene('broken_srl', tag='AI + AI', tagClass='base', title='AI signal (sumo-rl state) + AI cars, no TSI-G', delay=32.53,
                     caption='The AI cars glide toward a red instead of stopping. The signal\'s state is built from queued (stopped) cars, so gliding cars barely register and wait longer.'),
    fixed_srl=scene('fixed_srl', tag='AI + AI + TSI-G', tagClass='ai', title='Same signal, same cars, plus TSI-G', delay=26.31,
                    caption='TSI-G shows the signal each AI car as the human driver it replaces (a calibrated twin), so gliding cars count again. Neither AI is retrained.'),
    broken=scene('broken', tag='AI + AI', tagClass='base', title='AI signal (MPLight state) + AI cars, no TSI-G', delay=39.6,
                  caption='DQN with RESCO MPLight\'s state and reward: a pressure built from queued cars. The gliding AI cars hardly add pressure, so their approach is served last.'),
    fixed=scene('fixed', tag='AI + AI + TSI-G', tagClass='ai', title='Same signal, same cars, plus TSI-G', delay=28.0,
                caption='With TSI-G the gliding AI cars add pressure like the human drivers they replace. Most of the harm is removed, though not all of it.'),
    today=scene('today', tag='Baseline', tagClass='base', title='Fixed-time signals (SUMO-generated plan)', allHuman=True, delay=56.4,
                caption='Signals run a fixed cycle no matter who is waiting.'),
    best=scene('best', tag='AI + AI', tagClass='ai', title='AI signals + AI cars with a signal forecast', delay=16.7,
               caption='The signals see where the queue is; the cars know when green is coming and roll up as it turns.'),
)
views = dict(
    mt=dict(label='Midtown Manhattan', count='567 signals · full street map', net='mt', metricAI=False, legendAI=False, first='best',
            sub='The full street map of Midtown Manhattan, river to river. Signals controlled by AI that learned on a small 16-signal grid and had never seen this city.',
            cmps=dict(best=dict(label='Actuated signals → AI signals + AI cars', left='mtf0_act', right='mtf0_best', cards=mt_cards(act, BG),
                                foot=mt_foot_best.format(base='actuated', bt=tel([act]))),
                      act=dict(label='Actuated signals → AI signals (human drivers)', left='mtf0_act', right='mtf0_light', cards=mt_cards(act),
                               foot=mt_foot.format(base='actuated', bt=tel([act]))),
                      ft=dict(label='Fixed-time signals → AI signals + AI cars', left='mtf0_ft', right='mtf0_best', cards=mt_cards(ft, BG),
                              foot=mt_foot_best.format(base='fixed-time', bt=tel([ft])))),
            chart=dict(kind='dots', title='Delay per trip on the 5 test days (each dot one run)', unit='s per trip',
                       note='AI signals: 5 independently trained models × 5 days; with AI cars: × 4 independently trained fleets. Vertical bar: mean. Same traffic for every row.',
                       rows=[dict(label='Fixed-time (SUMO plan)', points=[round(ft[d]['timeloss'], 1) for d in days], mean=round(m1(ft, 'timeloss'), 1)),
                             dict(label='Actuated (SUMO)', points=[round(act[d]['timeloss'], 1) for d in days], mean=round(m1(act, 'timeloss'), 1)),
                             dict(label='AI signals (5 models)', ai=True, points=[round(r[d]['timeloss'], 1) for r in LG for d in days], mean=round(mL('timeloss'), 1)),
                             dict(label='AI signals + AI cars (5 × 4 models)', ai=True, points=[round(r[d]['timeloss'], 1) for r in BG for d in days], mean=round(mG(BG, 'timeloss'), 1))])),
    ai2=dict(label='Two AIs meet', count='the fix: TSI-G', net='grid', metricAI=True, legendAI=True, first='srl',
             sub='An AI signal and a fleet of AI eco-driving cars, each trained on its own. Put together, the signal stops seeing the AI cars. TSI-G fixes the mismatch without retraining either one.',
             cmps=dict(
                 srl=dict(label='sumo-rl state: without → with TSI-G', left='broken_srl', right='fixed_srl', cards=[
                     dict(big='+5.4 → −0.2 s', what='extra delay of AI cars from the mismatch', **{'from': 'per AI-car trip; repair limit met'}),
                     dict(big='−7.9%', what='AI-car fuel', **{'from': 'vs the same cars without the forecast'}),
                     dict(big='−2.5 s', what='delay per trip, whole city', **{'from': 'with vs without TSI-G'})],
                     foot=('Grid panel: 20 traffic days × 5 signal models × 4 AI fleets, crossed bootstrap. Signal: our DQN with the sumo-rl default state. Extra delay = AI-car time loss '
                           'minus the same signal and cars without the forecast service. Human drivers: +0.5 s per trip vs without TSI-G (the mismatch had favoured them). '
                           'Panel cards above; the clip (seed 1400, minutes 25–30) shows one run: AI-car delay 32.5 → 26.3 s.')),
                 rmp=dict(label='MPLight state: without → with TSI-G', left='broken', right='fixed', cards=[
                     dict(big='+16.0 → +0.5 s', what='extra delay of AI cars from the mismatch', warn=True, **{'from': 'per AI-car trip; 97% removed, last 0.5 s remains'}),
                     dict(big='−9.6%', what='AI-car fuel', **{'from': 'vs the same cars without the forecast'}),
                     dict(big='−8.2 s', what='delay per trip, whole city', **{'from': 'with vs without TSI-G'})],
                     foot=('Grid panel: 20 traffic days × 5 signal models × 4 AI fleets. Signal: our DQN with RESCO MPLight\'s state and reward representation. A large partial repair: '
                           'the pre-registered limit on the remaining AI-car delay (upper bound +0.74 s) was not met. The clip (seed 1400) shows one run: AI-car delay 39.6 → 28.0 s.'))),
             chart=dict(kind='ba', title='Extra delay of AI cars from the mismatch, five signal designs: without (red) → with TSI-G', unit='s per AI-car trip',
                        note='Shaded: 95% interval with TSI-G; green = met the pre-registered repair limit, amber = not met. The wave state counts every car, so it has no mismatch to fix (control).',
                        rows=[dict(label='Our signal (halting counts)', a=1.70, b=-0.28, lo=-0.42, hi=-0.14, **{'pass': True}),
                              dict(label='sumo-rl default state', a=5.36, b=-0.18, lo=-0.77, hi=0.33, **{'pass': True}),
                              dict(label='RESCO IDQN / IPPO state', a=2.63, b=-0.23, lo=-0.37, hi=-0.09, **{'pass': True}),
                              dict(label='RESCO MPLight state', a=16.02, b=0.51, lo=0.30, hi=0.71, **{'pass': False}),
                              dict(label='Wave state (control)', a=-1.05, b=-1.05, lo=-1.21, hi=-0.87, **{'pass': True})])),
    grid=dict(label='Test grid', count='16 signals', net='grid', metricAI=False, legendAI=True, first='best',
              sub='The 16-signal grid where the AIs learned: fixed-time signals vs AI signals with AI eco-driving cars.',
              cmps=dict(best=dict(label='Fixed-time → AI signals + AI cars', left='today', right='best', cards=[
                  dict(big='−71%', what='delay per trip', **{'from': '55.8 → 16.2 seconds'}), dict(big='−93%', what='time stopped per trip', **{'from': '39.1 → 2.7 seconds'}),
                  dict(big='−26%', what='fuel per trip', **{'from': '93.8 → 69.8 grams'})],
                  foot='Grid panel: 20 unseen traffic days × 5 AI signal models × 4 AI fleets, fuel model HBEFA4. Baseline: SUMO-generated fixed-time plan. Clip: seed 1400, minutes 25–30.')),
              chart=dict(kind='dots', title='Delay per trip, panel means', unit='s per trip', note='Means over the evaluation panel.',
                         rows=[dict(label='Fixed-time (SUMO plan)', points=[55.8], mean=55.8), dict(label='AI signals + AI cars', ai=True, points=[16.2], mean=16.2)])),
)
views['mt']['zoom'] = busiest_box(nets['mt'], ['mtf0_act', 'mtf0_best'], 650.0)
views['ai2']['zoom'] = busiest_box(nets['grid'], ['broken_srl', 'fixed_srl'], 440.0)
views['grid']['zoom'] = busiest_box(nets['grid'], ['today', 'best'], 440.0)
data = dict(nets=nets, scenes=scenes, views=views, order=['mt', 'ai2', 'grid'])
if (D / 'data/train_light.json').exists() and (D / 'data/train_fleet.json').exists():
    lt = J(D / 'data/train_light.json'); fl = J(D / 'data/train_fleet.json')
    lc = [r['mean_r'] for r in J(ROOT / 'research/city_sim/w19_20261008/lights/RL-H_t59.log.json')]
    fc = [float(x.group(1)) for x in re.finditer(r' ep \d+ .*?meanR (-?[\d.]+)', (ROOT / 'research/city_sim/w15_20261007/fresh3/fleets/L11_s1413.out').read_text())]
    data['train'] = dict(net='grid', light=dict(episodes=lt['episodes'], tls=lt['tls'], n=len(lc), curve=smooth(lc), label='light reward per decision, rising = less delay'),
                         fleet=dict(episodes=fl['episodes'], tls=fl['tls'], n=len(fc), curve=smooth(fc), label='car reward per decision, rising = less fuel'))
blob = json.dumps(data, separators=(',', ':'), ensure_ascii=False).replace('</', '<\\/')
html = (D / 'page_template.html').read_text().replace('__DATA__', blob)
(D / 'gridlock_to_green.html').write_text(html)
print('wrote', D / 'gridlock_to_green.html', round(len(html.encode()) / 2 ** 20, 2), 'MB; views', data['order'], '; zoom', {k: v['zoom'] for k, v in views.items()})
for k in ('act', 'ft'):
    print('midtown', k, [(c['big'], c['from']) for c in views['mt']['cmps'][k]['cards']], views['mt']['cmps'][k]['foot'][-260:-120])
