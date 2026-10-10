"""Wave-6 audit: strict data loading before any statistical verdict. No resampling here."""
import json, math
from pathlib import Path
PRIMARY = ('fuel_agent', 'timeloss', 'timeloss_agent', 'timeloss_human')
def rows(directory):
    out = {}
    for p in sorted(Path(directory).glob('*.json')):
        d = json.loads(p.read_text())
        if not isinstance(d, dict) or 'rows' not in d: continue
        if d.get('status') != 'COMPLETE': raise ValueError(f'INCOMPLETE {p}')
        rr = d['rows']; seeds = [r['seed'] for r in rr]
        if len(seeds) != len(set(seeds)): raise ValueError(f'DUPLICATE SEED {p}')
        for r in rr:
            for k in ('teleports', 'unfinished'):
                if k not in r or not math.isfinite(r[k]) or r[k] < 0: raise ValueError(f'INVALID COUNT {p} {k}')
        out[p.stem] = {r['seed']:r for r in rr}
    return out

def require_panel(data, keys, seeds, metrics=PRIMARY):
    for key in set(keys):
        if key not in data or set(data[key]) != set(seeds): raise ValueError(f'INCOMPLETE/EXTRA SEEDS {key}')
        for s in seeds:
            for m in metrics:
                if m not in data[key][s] or not math.isfinite(data[key][s][m]): raise ValueError(f'NONFINITE/MISSING {key} {s} {m}')
                if m == 'fuel_agent' and data[key][s][m] <= 0: raise ValueError(f'NONPOSITIVE FUEL {key} {s}')
