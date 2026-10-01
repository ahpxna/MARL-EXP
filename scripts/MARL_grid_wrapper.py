#!/usr/bin/env python3
"""Run an unchanged E3 script on a ROWS x COLS grid (30/09 20:3x EDT; ledger L-186; user 20:0x: "expand the map, no more 3x3").
The E3 scripts build scenarios through scripts.MARL_hetero_target_diag.scenario, which reads the module globals ROWS / COLS
at call time.  This wrapper sets them before the script runs, so the 3x3 scripts (used by running jobs) are not edited and
their source hashes do not change.  Usage:
  python -u scripts/MARL_grid_wrapper.py --rows 4 --cols 4 -- scripts/<script>.py <its arguments>
The wrapper records the grid in <out>.grid.json (next to the output directory) when the script has an --out argument.
"""
import json, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
argv = sys.argv[1:]
sep = argv.index('--')
rows = int(argv[argv.index('--rows') + 1]); cols = int(argv[argv.index('--cols') + 1])
script, rest = argv[sep + 1], argv[sep + 2:]
import scripts.MARL_hetero_target_diag as TD
import scripts.MARL_hetero_pilot_collect as PC
TD.ROWS, TD.COLS = rows, cols
PC.ROWS, PC.COLS = rows, cols
# The set actor's agent count defaults to 9 (hidden=128, m=9, own_dim=35, blk_dim=29); trainers construct it without m.
import models.marl_comm_actor_set as SA
_d = list(SA.SetActorNet.__init__.__defaults__)
assert _d[1] == 9, _d
_d[1] = rows * cols
SA.SetActorNet.__init__.__defaults__ = tuple(_d)
if '--out' in rest:
    out = Path(rest[rest.index('--out') + 1]); out.parent.mkdir(parents=True, exist_ok=True)
    Path(str(out) + '.grid.json').write_text(json.dumps(dict(rows=rows, cols=cols, script=script, args=rest)))
sys.argv = [script] + rest
runpy.run_path(script, run_name='__main__')
