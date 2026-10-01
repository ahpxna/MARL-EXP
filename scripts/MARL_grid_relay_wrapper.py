#!/usr/bin/env python3
"""Run an unchanged E3 relay script (student training / evaluation) on a ROWS x COLS grid with a fixed relay slot set
(30/09 20:4x EDT; ledger L-186).

The grid part is exactly scripts/MARL_grid_wrapper.py: the scenario globals ROWS / COLS of
scripts.MARL_hetero_target_diag and scripts.MARL_hetero_pilot_collect, and the set actor's default agent count (asserted
to be 9 before patching).  The relay part replaces, in memory and before the script imports them,
  * models.marl_relay_v2.merge_views  by models.marl_relay_v3.make_slot_merge(slots), and
  * models.marl_delivery_music.AgeMirror by models.marl_relay_v3.make_slot_mirror(slots),
so the script's own code, self-checks (mirror == merged views at every step, oracle-access audit, byte accounting,
parity), codebooks and age saturation are all unchanged.  Files on disk are not modified (the scripts' source-hash checks
are unaffected).  --relay-slots all reproduces v2 exactly; nearest8 keeps the 185-bit 25 B layout for any team size.
Usage:
  python -u scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 -- scripts/<script>.py <args>
"""
import json, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
argv = sys.argv[1:]
sep = argv.index('--')
opts = argv[:sep]
rows = int(opts[opts.index('--rows') + 1]); cols = int(opts[opts.index('--cols') + 1])
mode = opts[opts.index('--relay-slots') + 1]
script, rest = argv[sep + 1], argv[sep + 2:]
import scripts.MARL_hetero_target_diag as TD
import scripts.MARL_hetero_pilot_collect as PC
TD.ROWS, TD.COLS = rows, cols
PC.ROWS, PC.COLS = rows, cols
import models.marl_comm_actor_set as SA
_d = list(SA.SetActorNet.__init__.__defaults__)
assert _d[1] == 9, _d
_d[1] = rows * cols
SA.SetActorNet.__init__.__defaults__ = tuple(_d)
import models.marl_relay_v2 as RV2
import models.marl_delivery_music as MUSIC
import models.marl_relay_v3 as RV3
m = rows * cols
if mode == 'all':
    slots = {k: frozenset(j for j in range(m) if j != k) for k in range(m)}
elif mode.startswith('nearest'):
    slots = RV3.nearest_slots(rows, cols, int(mode[len('nearest'):]))
else:
    raise SystemExit(f'unknown --relay-slots {mode}')
RV2.merge_views = RV3.make_slot_merge(slots)
MUSIC.AgeMirror = RV3.make_slot_mirror(slots)
if '--out' in rest:
    out = Path(rest[rest.index('--out') + 1]); out.parent.mkdir(parents=True, exist_ok=True)
    Path(str(out) + '.grid.json').write_text(json.dumps(dict(rows=rows, cols=cols, relay_slots=mode, script=script, args=rest,
                                                            slots={str(k): sorted(v) for k, v in slots.items()})))
sys.argv = [script] + rest
runpy.run_path(script, run_name='__main__')
