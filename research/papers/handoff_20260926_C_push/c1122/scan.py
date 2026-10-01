import sys
import numpy as np
from lp import solve
rs = [float(x) for x in np.round(np.arange(1.05, 6.001, 0.05), 4)]
etas = [float(x) for x in np.round(np.arange(0, 2.0001, 0.02), 4)]
import json
out = {}
for r in rs:
    vals = [solve(r, e) for e in etas]
    out[r] = vals
    free = vals[-1]
    # breakpoints via second differences
    kinks = []
    for i in range(1, len(etas) - 1):
        sd = vals[i - 1] - 2 * vals[i] + vals[i + 1]
        if abs(sd) > 1e-7:
            kinks.append(etas[i])
    print(f"r={r:.2f} T0={vals[0]:.6f} Tfree={free:.6f} price={vals[0]/free if free>1e-12 else float('nan'):.5f} kinks={kinks}", flush=True)
json.dump({"etas": etas, "rows": out}, open("scan.json", "w"))
