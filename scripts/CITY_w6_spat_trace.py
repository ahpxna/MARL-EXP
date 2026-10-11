"""Independent SP3 check against realized phase history; no use of forecast durations."""
from bisect import bisect_right

def check_queries(trace, states, queries):
    checked = bad = censored = 0; changes = {}; examples = []
    for t, tid, link, prediction in queries:
        key = (tid,link)
        if key not in changes:
            p = trace[tid]; times = sorted(p)
            changes[key] = [s for s in times if states[tid][p[s]][link] in 'Gg']
        greens = changes[key]; ix = bisect_right(greens,t)
        if ix == len(greens): censored += 1; continue
        observed = greens[ix] - t
        checked += 1; bad += abs(observed - prediction) > 0.5
        if abs(observed-prediction)>0.5 and len(examples)<6:
            examples.append(dict(t=t,tid=tid,link=link,predicted=prediction,observed=observed,phase=trace[tid].get(t),states=[s[link] for s in states[tid]]))
    return dict(checked=checked, mismatches=bad, censored=censored, examples=examples)
