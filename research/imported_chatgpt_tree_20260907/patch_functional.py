from pathlib import Path
p=Path('work/code/run_functional_variance_stopping_lab.py');s=p.read_text().replace('functional_variance_stopping_v2_balanced_batches','functional_variance_stopping_v3_weighted_shrink_exploration')
a=s.index('    if variant in {"C_pilot", "C_shrink", "C_split"}:',s.index('def _allocate_batch'))
b=s.index('\n\ndef _one_variant',a)
s=s[:a]+'''    # Every adaptive policy reserves >=20% of each batch for the least-sampled
    # cells. A cell cannot remain at its initial count while sampling continues.
    working = counts.copy()
    explore = min(int(n_add), int(math.ceil(0.2 * int(n_add))))
    for _ in range(explore):
        cell = int(np.argmin(working))
        draw.flat[cell] += 1
        working.flat[cell] += 1

    if variant in {"C_pilot", "C_shrink", "C_split"}:
        drivers = fixed_drivers or [(r, a) for r in range(R) for a in range(K)]
        scale = np.maximum(np.asarray(fixed_scale if fixed_scale is not None else sigmas, float), 1e-12)
        # Greedily reduce sum_i sigma_i^2/n_i. The marginal gain is
        # sigma_i^2/[n_i(n_i+1)], so magnitudes affect allocation (Neyman rule).
        # Pilot and shrink use exactly the same drivers/exploration policy.
        for _ in range(int(n_add) - explore):
            cell = max(drivers, key=lambda x: (
                float(scale[x]) ** 2 / (float(working[x]) * (float(working[x]) + 1)),
                -x[0], -x[1]))
            draw[cell] += 1
            working[cell] += 1
        return draw

    scores = np.ptp(means, axis=1)
    chosen = np.argsort(-scores, kind="stable")[: int(k)]
    c_lo, c_hi = _capacity_intervals(lower, upper)
    threshold = float(np.min(c_lo[chosen]))
    candidates = [r for r in range(R) if r in set(chosen) or c_hi[r] >= threshold]
    drivers = _driver_cells(means, lower, upper, candidates)
    for _ in range(int(n_add) - explore):
        cell = max(drivers, key=lambda x: (float(sigmas[x]) / math.sqrt(float(working[x])), -x[0], -x[1]))
        draw[cell] += 1
        working[cell] += 1
    return draw
''' +s[b:]
s=s.replace('    emitted = False\n', '    initial_counts = counts.copy()\n    emitted = False\n',1)
s=s.replace('        "counts": counts.tolist(),','''        "counts": counts.tolist(),
        "initial_counts": initial_counts.tolist(),
        "minimum_cell_samples": int(counts.min()),
        "cells_at_initial_count": int(np.sum(counts == initial_counts)),
        "true_topk_gap": float(np.sort(np.ptp(truth, axis=1))[::-1][k-1] - np.sort(np.ptp(truth, axis=1))[::-1][k]),
        "final_capacity_lower": c_lo.tolist(),
        "final_capacity_upper": c_hi.tolist(),
        "final_certificate_margin": float(np.min(c_lo[chosen]) - np.max(c_hi[[r for r in range(R) if r not in set(chosen)]])),''')
s=s.replace('    if not 0.10 <=', '''    if int(batch) < 1 or int(instances) < 1 or not seeds:
        raise ValueError("positive batch/instances and nonempty seeds are required")
    if not 1 <= int(topk) < int(relations):
        raise ValueError("topk must satisfy 1 <= topk < relations")
    if not 0.10 <=''')
s=s.replace('"continuous uniform batches; least-sampled exploration"','"uniform round-robin; >=20% least-sampled exploration for every adaptive policy; fixed-driver exploitation maximizes sigma^2/[n(n+1)]"')
p.write_text(s)
