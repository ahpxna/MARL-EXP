#!/usr/bin/env python3
"""Run an unchanged E3 script on the NYC 16x3 network (02/10/2026 22:4x EDT; PROTOCOL_E3_NYC16X3_20261002.md).

As scripts/MARL_grid_wrapper.py / MARL_grid_relay_wrapper.py, with the scenario factory replaced: the module global
make_grid_scenario of scripts.MARL_hetero_target_diag and scripts.MARL_hetero_pilot_collect (looked up at call time by their
scenario functions) becomes scripts.MARL_nyc_scenario.make_nyc_scenario; ROWS / COLS = 16 / 3; the set actor's default agent
count 9 -> 48 (asserted before patching).  --relay-slots nearest8 also patches the relay merge and the age mirror with the 8
nearest agents by grid index read from the intersection ids (scripts.MARL_nyc_scenario.nearest_slots); --relay-slots none leaves
them alone (teacher / Z training and evaluation).  Files on disk are not modified.
Usage: python -u scripts/MARL_nyc_wrapper.py --relay-slots {none,nearest8} -- scripts/<script>.py <its arguments>
"""
import json, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
argv = sys.argv[1:]
sep = argv.index('--'); opts = argv[:sep]
mode = opts[opts.index('--relay-slots') + 1] if '--relay-slots' in opts else 'none'
script, rest = argv[sep + 1], argv[sep + 2:]
import scripts.MARL_nyc_scenario as NYC
import scripts.MARL_hetero_target_diag as TD
import scripts.MARL_hetero_pilot_collect as PC
TD.ROWS, TD.COLS = 16, 3
PC.ROWS, PC.COLS = 16, 3
TD.make_grid_scenario = NYC.make_nyc_scenario
PC.make_grid_scenario = NYC.make_nyc_scenario
import models.marl_comm_actor_set as SA
_d = list(SA.SetActorNet.__init__.__defaults__)
assert _d[1] == 9, _d
_d[1] = 48
SA.SetActorNet.__init__.__defaults__ = tuple(_d)
slots = None
if mode == 'nearest8':
    import models.marl_relay_v2 as RV2
    import models.marl_delivery_music as MUSIC
    import models.marl_relay_v3 as RV3
    slots = NYC.nearest_slots(8)
    RV2.merge_views = RV3.make_slot_merge(slots)
    MUSIC.AgeMirror = RV3.make_slot_mirror(slots)
elif mode != 'none':
    raise SystemExit(f'unknown --relay-slots {mode}')
if '--out' in rest:
    out = Path(rest[rest.index('--out') + 1]); out.parent.mkdir(parents=True, exist_ok=True)
    Path(str(out) + '.grid.json').write_text(json.dumps(dict(network='nyc16x3', rows=16, cols=3, relay_slots=mode, script=script, args=rest,
                                                            data_sha256=NYC.HASHES, mu={'8': NYC.mu(8), '16': NYC.mu(16)},
                                                            slots={str(k): sorted(v) for k, v in slots.items()} if slots else None)))
sys.argv = [script] + rest
runpy.run_path(script, run_name='__main__')
