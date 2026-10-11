#!/usr/bin/env python3
"""NYC-like fixed-time plan for the Midtown net (10/10/2026; user: "cái Today ... có bám sát với thực tế ko? ... dùng config giống với thực tế
hơn ko?").  The netconvert plan ("Today" so far) gives every one of the 248 signals a 90 s cycle, an even avenue / street split and offset 0
(no coordination).  Manhattan practice: pre-timed signals, cycles of about 90 s, more green for the avenues, and coordinated progression
along the one-way avenues.  This builds that plan with SUMO's own tools, tuned on TRAINING traffic only (seed 10, never a test seed):
  1. splits: tlsCycleAdaptation.py (Webster, -e existing cycle) on midtown_p075_s10; only its GREEN RATIOS are used: every yellow / red
     phase keeps its original duration, and the greens are rescaled so that every cycle is exactly 90 s (minimum green 10 s);
  2. offsets: tlsCoordinator.py on the same training routes (green waves along the main flows; it writes offsets only), taken modulo
     90 s and merged into the plan of step 1.
Phase structure (states, order) is unchanged, so the learned light and the SPaT forecasts see the same programs as before.
Output: research/city_sim/midtown_transfer_20261010/nyc_timing/nyc.add.xml (programID 'nyc'; loaded with -a it becomes the active program).
Usage: MT_nyc_timing.py"""
import os, subprocess, sys
from pathlib import Path
from xml.etree import ElementTree as ET
import sumolib

ROOT = Path(__file__).resolve().parents[1]; NET = ROOT / 'research/city_sim/net/midtown.net.xml'; ROU = ROOT / 'research/city_sim/demand/midtown_p075_s10.rou.xml'
OUT = ROOT / 'research/city_sim/midtown_transfer_20261010/nyc_timing'; TOOLS = Path(sumolib.__file__).resolve().parents[1] / 'sumo/tools'; CYCLE, GMIN = 90.0, 10.0
is_green = lambda s: ('G' in s or 'g' in s) and 'y' not in s.lower()


def main():
    OUT.mkdir(parents=True, exist_ok=True); env = dict(os.environ, SUMO_HOME=str(TOOLS.parent))
    web = OUT / 'webster_s10.add.xml'
    subprocess.run([sys.executable, str(TOOLS / 'tlsCycleAdaptation.py'), '-n', str(NET), '-r', str(ROU), '-b', '0', '-e', '-p', 'webster', '-o', str(web)],
                   check=True, env=env, capture_output=True)
    net = sumolib.net.readNet(str(NET), withPrograms=True)
    orig = {t.getID(): [(p.state, float(p.duration)) for p in list(t.getPrograms().values())[0].getPhases()] for t in net.getTrafficLights()}
    W = {tl.get('id'): [float(p.get('duration')) for p in tl.iter('phase')] for tl in ET.parse(web).getroot().iter('tlLogic')}
    add = ET.Element('additional'); changed = 0
    for tid in sorted(orig):
        ph = orig[tid]; gi = [i for i, (s, _) in enumerate(ph) if is_green(s)]; dur = [d for _, d in ph]
        if len(gi) >= 2 and tid in W and len(W[tid]) == len(ph):
            avail = CYCLE - sum(d for i, d in enumerate(dur) if i not in gi); w = [max(W[tid][i], 1e-6) for i in gi]
            g = [avail * x / sum(w) for x in w]
            for _ in range(10):                                    # minimum green, keep the sum
                low = [k for k, x in enumerate(g) if x < GMIN]
                if not low:
                    break
                rest = [k for k in range(len(g)) if k not in low]; spare = avail - GMIN * len(low)
                g = [GMIN if k in low else spare * g[k] / sum(g[j] for j in rest) for k in range(len(g))]
            g = [round(x) for x in g]; g[0] += round(avail) - sum(g)  # integer seconds, cycle exactly 90
            for k, i in enumerate(gi):
                dur[i] = float(g[k])
            changed += 1
        tl = ET.SubElement(add, 'tlLogic', id=tid, type='static', programID='nyc', offset='0')
        for (s, _), d in zip(ph, dur):
            ET.SubElement(tl, 'phase', duration=f'{d:g}', state=s)
    split = OUT / 'nyc_split.add.xml'; ET.ElementTree(add).write(split)
    coord = OUT / 'coord_offsets.add.xml'; final = OUT / 'nyc.add.xml'
    subprocess.run([sys.executable, str(TOOLS / 'tlsCoordinator.py'), '-n', str(NET), '-r', str(ROU), '-a', str(split), '-o', str(coord)], check=True, env=env,
                   capture_output=True)
    off = {tl.get('id'): float(tl.get('offset')) for tl in ET.parse(coord).getroot().iter('tlLogic')}   # the coordinator writes offsets only
    for tl in add.iter('tlLogic'):
        tl.set('offset', f"{off.get(tl.get('id'), 0.0) % CYCLE:.2f}")
    ET.ElementTree(add).write(final)
    # checks: same states, original non-green durations, cycle 90 s, offsets present
    R = ET.parse(final).getroot(); n = 0; offs = 0; bad = []
    for tl in R.iter('tlLogic'):
        ph = [(p.get('state'), float(p.get('duration'))) for p in tl.iter('phase')]; o = orig[tl.get('id')]; n += 1
        offs += float(tl.get('offset', 0)) != 0
        if [s for s, _ in ph] != [s for s, _ in o] or any(abs(d - od) > 1e-9 for (s, d), (_, od) in zip(ph, o) if not is_green(s)) or \
                (len([s for s, _ in o if is_green(s)]) >= 2 and abs(sum(d for _, d in ph) - CYCLE) > 1e-9):
            bad.append(tl.get('id'))
    print(f'nyc plan: {n} signals, {changed} re-split, {offs} with a non-zero offset, {len(bad)} failing checks {bad[:5]} -> {final}', flush=True)
    sys.exit(1 if bad or n != len(orig) else 0)


if __name__ == '__main__':
    main()
