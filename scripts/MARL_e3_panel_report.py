#!/usr/bin/env python3
"""E3 panel reporter (handoff MARL_REMAINING_WORK_HANDOFF_20260928_1910 W2): the statistical report of the closed-loop
panels across actors, from the raw rows.  Read-only (rows.json, manifests, configs, checkpoints); no rollouts.

Units, never conflated:
  actor seed     the replication unit of a recipe claim (across actors: two-level bootstrap, actors then traffic seeds);
  selector init  s0/s1/s2 of one selector recipe: AVERAGED within an actor and episode, never a replication;
  traffic seed   the cluster inside an actor: both loads (headways) of a seed are resampled together;
  load, method, cap, capacity model, checkpoint sha256: recorded for every run.
Comparisons, paired by episode inside ONE actor (different actors are never paired state by state):
  actor_vs_mp2        prefix vs mp2: the actor's competence, NOT evidence for a selector;
  selector_vs_prefix  each selector recipe vs the same actor's committed prefix (the selection effect);
  selector_vs_direct  each selector recipe vs the direct no-bid selector (--direct, default sel_nobid);
  bid_vs_samebyte     a bid recipe vs a same-byte control (--samebyte BID:CONTROL; only when both ran in the run).
Endpoints (lower is better unless marked): waiting = queue_sum, the registered primary (sum of the queue over the
decisions); guardrails finished vehicles (higher), unfinished vehicles, throughput per hour (higher), mean travel
time of finished trips, CityFlow's censored travel time; resources charged bytes, edits, revisions, clipped fields.
A field missing from the rows is reported MISSING; it is never derived from waiting.
Assertions (any failure: status FAIL, exit 2, and no comparison is reported):
  * manifest COMPLETE (and self_check PASS when recorded); the traffic seeds are not the reserved test seeds
    1301-1316 unless --final;
  * every method x selector init present on exactly the manifest's traffic seeds x headways, no duplicate
    (method, episode); one cap and one capacity model, equal to the manifest's;
  * charged bytes == payload + request + 10 B x decisions for bid / queue-bid arms (+0 otherwise);
  * prefix and mp2 make no edits and no revisions; zero oracle access in every deployable row (a method named
    oracle* is a diagnostic: kept out of every comparison);
  * every selector checkpoint of the run exists, its job was trained on labels of THIS actor's checkpoint, and it
    is not newer than the closed-loop manifest; the run's actor checkpoint is this actor's; the actor's recipe
    (scratch / bc / mix / warm, from config.json) equals the declared group.
Per-step cap compliance is enforced inside the runtime (closed loop v5 also asserts per-step byte parity); the rows
carry episode totals only, so this reporter does not claim to re-verify it.
Optional offline decision metrics (--diag NAME, e.g. selectors_v2_diag_v3.json): only selector diagnostic v3 files
(tie-half pair accuracy) are accepted; a v2 file (strict pair metric) is refused.
Output: --out (JSON: per-actor and across-actor statistics, the assertion log, a source manifest with the sha256 of
every input and of this file) and --out-txt.
Usage: MARL_e3_panel_report.py --actor scratch:claim:DIR [--actor bc:descriptive:DIR ...] [--cl cl_v3_direct]
         [--direct sel_nobid] [--samebyte sb_top2bid:sb_queuebid] [--diag selectors_v2_diag_v3.json] --out X.json --out-txt X.txt
Self-test (--selftest): synthetic rows with a known effect, then each assertion is broken once and must fail.
"""
from __future__ import annotations
import argparse, hashlib, json, re, sys
from collections import defaultdict
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
BID_BYTES = 10
TEST_SEEDS = set(range(1301, 1317))
S = lambda r: r.get('summary') or {}
ENDPOINTS = [   # name, getter, direction (+1 higher is better, -1 lower is better, 0 resource)
    ('waiting', lambda r: r.get('queue_sum'), -1),
    ('finished_vehicles', lambda r: S(r).get('finished_vehicles'), +1),
    ('unfinished_vehicles', lambda r: S(r).get('unfinished_vehicles'), -1),
    ('throughput_per_hour', lambda r: S(r).get('throughput_per_hour'), +1),
    ('travel_time_finished_mean', lambda r: S(r).get('travel_time_finished_mean'), -1),
    ('travel_time_censored', lambda r: S(r).get('travel_time_cityflow_censored'), -1),
    ('bytes', lambda r: r.get('bytes'), 0),
    ('edits', lambda r: r.get('edits'), 0),
    ('revisions', lambda r: S(r).get('revisions'), 0),
    ('clipped_fields', lambda r: S(r).get('clipped_fields'), 0),
]
_H = {}


def sha(p):
    p = Path(p).resolve()
    if p not in _H:
        _H[p] = hashlib.sha256(p.read_bytes()).hexdigest()
    return _H[p]


def parse_ep(ep):
    m = re.fullmatch(r'seed(\d+)_load(\d+(?:\.\d+)?)', ep)
    if not m:
        raise ValueError(f'unparsable episode id {ep!r}')
    return int(m.group(1)), float(m.group(2))


def parse_method(m):
    fam, _, init = m.partition('/')
    return fam, (init or None)


def recipe(cfg):
    if 'bc_epochs' in cfg:
        return 'bc'
    if float(cfg.get('p_mix') or 0) > 0:
        return 'mix'
    if cfg.get('init_from'):
        return 'warm'
    return 'scratch'


def gates(A):
    out = {}
    rp = A / 'msguse/report.json'
    if rp.exists():
        g = json.loads(rp.read_text()); n = g['none_vs_actual_pct']; rate = g['input_action_change_rate']['none']
        out['G1'] = {'pass': bool(rate >= 0.10 and n['mean'] > 0 and n['ci95'][0] > 0), 'none_vs_actual_pct': n, 'action_change_rate_none': rate}
    else:
        out['G1'] = 'MISSING'
    m = json.loads((A / 'manifest.json').read_text()) if (A / 'manifest.json').exists() else {}
    if 'best_select' in m and 'mp2_select' in m:
        out['G2'] = {'pass': bool(m['best_select'] <= 1.10 * m['mp2_select']), 'best_select': m['best_select'], 'mp2_select': m['mp2_select']}
    else:
        out['G2'] = 'MISSING'
    return out


def _cluster_means(vals_by_cluster, B, rng):
    """B bootstrap means of the pooled values, clusters resampled with replacement (mean of the concatenation)."""
    K = sorted(vals_by_cluster); s = np.array([np.sum(vals_by_cluster[k]) for k in K]); n = np.array([len(vals_by_cluster[k]) for k in K], float)
    idx = rng.integers(0, len(K), (B, len(K)))
    return s[idx].sum(1) / n[idx].sum(1)


def boot_cluster(vals_by_cluster, B=5000, seed=0):
    if not vals_by_cluster:
        return [np.nan, np.nan]
    return [float(x) for x in np.quantile(_cluster_means(vals_by_cluster, B, np.random.default_rng(seed)), [0.025, 0.975])]


def boot_two_level(actors, B=5000, seed=0):
    """actors: list of {traffic seed: array of per-episode values}; resample actors, then (independently for every
    draw of an actor) its traffic seeds; the replicate is the mean of the drawn actors' means."""
    rng = np.random.default_rng(seed); nA = len(actors)
    inner = np.stack([np.stack([_cluster_means(a, B, rng) for _ in range(nA)], 1) for a in actors])   # (actor, B, draw slot)
    pick = rng.integers(0, nA, (B, nA))
    rep = inner[pick, np.arange(B)[:, None], np.arange(nA)[None, :]].mean(1)
    return [float(x) for x in np.quantile(rep, [0.025, 0.975])]


class Check:
    def __init__(self):
        self.log = []

    def __call__(self, ok, what):
        self.log.append({'ok': bool(ok), 'check': what})
        return bool(ok)

    @property
    def failed(self):
        return [c['check'] for c in self.log if not c['ok']]


def load_run(A, cl, group, final, chk):
    """Validate one actor's closed-loop run; return (rows by (family, init, episode), run info)."""
    C = A / cl; man = json.loads((C / 'manifest.json').read_text()); rows = json.loads((C / 'rows.json').read_text())
    args = man.get('args', {})
    chk(man.get('status') == 'COMPLETE', f'{C}: manifest COMPLETE')
    if 'self_check' in man:
        chk(man['self_check'] == 'PASS', f'{C}: runtime self_check PASS')
    cfg = json.loads((A / 'config.json').read_text()); rec = recipe(cfg)
    chk(rec == group, f'{A}: actor recipe {rec} == declared group {group}')
    actor_ck = Path(args.get('actor', ''))
    chk(actor_ck.exists() and actor_ck.resolve() == (A / 'ckpt_best.pt').resolve(), f'{C}: run actor checkpoint is {A}/ckpt_best.pt')
    seeds = [int(s) for s in args.get('traffic_seeds', [])]; heads = [float(h) for h in args.get('headways', [8.0, 16.0])]
    chk(len(seeds) > 0, f'{C}: manifest lists traffic seeds')
    if not final:
        chk(not (set(seeds) & TEST_SEEDS), f'{C}: no reserved test seed 1301-1316 (use --final only after the freeze)')
    expected_eps = {f'seed{s}_load{h:g}' for s in seeds for h in heads}
    cap = args.get('cap'); capacity = args.get('capacity')
    by = {}; dup = 0; fams = defaultdict(set)
    for r in rows:
        fam, init = parse_method(r['method']); key = (fam, init, r['episode'])
        dup += key in by; by[key] = r; fams[fam].add(init)
    chk(dup == 0, f'{C}: no duplicate (method, episode) rows ({dup} found)')
    for fam, inits in fams.items():
        for init in inits:
            eps = {k[2] for k in by if k[0] == fam and k[1] == init}
            chk(eps == expected_eps, f'{C}: {fam}{"/" + init if init else ""} covers exactly the {len(expected_eps)} declared episodes (has {len(eps)})')
    chk({r['cap'] for r in rows} == {cap}, f'{C}: one cap per run, equal to the manifest ({cap})')
    chk({r.get('capacity') for r in rows} == {capacity}, f'{C}: one capacity model, equal to the manifest ({capacity})')
    for need in ('prefix',):
        chk(need in fams, f'{C}: method {need} present')
    # selector checkpoints, recipe and byte accounting
    sel_dirs = args.get('selectors', []); sel_dirs = [sel_dirs] if isinstance(sel_dirs, str) else list(sel_dirs)
    man_mtime = (C / 'manifest.json').stat().st_mtime; ckpts = {'actor': {'path': str(actor_ck), 'sha256': sha(actor_ck) if actor_ck.exists() else None}}
    bid_of = {}
    for fam, inits in fams.items():
        if fam in ('prefix', 'mp2') or fam.startswith('oracle'):
            continue
        for init in inits:
            mf = [Path(d) / f'model_{fam}_{init}.pt' for d in sel_dirs if (Path(d) / f'model_{fam}_{init}.pt').exists()]
            jf = [Path(d) / f'job_{fam}_{init}.json' for d in sel_dirs if (Path(d) / f'job_{fam}_{init}.json').exists()]
            if not chk(len(mf) == 1 and len(jf) == 1, f'{C}: exactly one checkpoint and job for {fam}/{init} in {sel_dirs}'):
                continue
            job = json.loads(jf[0].read_text())
            chk(Path(job.get('actor_ckpt', '')).resolve() == (A / 'ckpt_best.pt').resolve(), f'{C}: {fam}/{init} trained on labels of {A}/ckpt_best.pt')
            chk(mf[0].stat().st_mtime <= man_mtime, f'{C}: {fam}/{init} checkpoint not newer than the closed-loop manifest')
            bid_of[(fam, init)] = bool(job.get('bid') or job.get('qbid'))
            ckpts[f'{fam}/{init}'] = {'path': str(mf[0]), 'sha256': sha(mf[0]), 'job': str(jf[0]), 'bid': bid_of[(fam, init)],
                                      'tau_direct': (job.get('results', {}).get('direct') or {}).get('tau')}
    bad_bytes = bad_edit = bad_oracle = 0
    for (fam, init, ep), r in by.items():
        s = S(r)
        if fam.startswith('oracle'):
            continue
        extra = BID_BYTES * int(s.get('decisions', 0)) if bid_of.get((fam, init)) else 0
        if not ('payload_bytes' in s and 'request_bytes' in s and r.get('bytes') == s['payload_bytes'] + s['request_bytes'] + extra):
            bad_bytes += 1
        if fam in ('prefix', 'mp2') and (r.get('edits', 0) != 0 or s.get('revisions', 0) != 0):
            bad_edit += 1
        al = s.get('access_log', {})
        if s.get('oracle_access_used') or any(v for v in al.values()):
            bad_oracle += 1
    chk(bad_bytes == 0, f'{C}: charged bytes == payload + request + bid bytes in every row ({bad_bytes} violations)')
    chk(bad_edit == 0, f'{C}: prefix and mp2 make no edits/revisions ({bad_edit} violations)')
    chk(bad_oracle == 0, f'{C}: zero oracle access in every deployable row ({bad_oracle} violations)')
    info = dict(closed_loop=str(C), rows_sha256=sha(C / 'rows.json'), manifest_sha256=sha(C / 'manifest.json'), runtime_source_hashes=man.get('source_hashes'),
                cap=cap, capacity=capacity, traffic_seeds=seeds, headways=heads, methods={f: sorted(i for i in v if i) or [None] for f, v in fams.items()},
                checkpoints=ckpts, recipe=rec, config_sha256=sha(A / 'config.json'), gates=gates(A))
    return by, info


def episode_means(by, fam):
    """{episode: {endpoint: value averaged over the family's selector inits}} (MISSING -> None)."""
    out = {}
    for ep in sorted({k[2] for k in by if k[0] == fam}):
        rs = [r for k, r in by.items() if k[0] == fam and k[2] == ep]; d = {}
        for name, get, _ in ENDPOINTS:
            v = [get(r) for r in rs]
            d[name] = None if any(x is None for x in v) else float(np.mean(v))
        out[ep] = d
    return out


def per_init(by, fam, ref_means):
    """Selector init level waiting difference vs the reference (transparency only; not replications)."""
    out = {}
    for init in sorted({k[1] for k in by if k[0] == fam and k[1]}):
        d = [100 * (by[(fam, init, ep)]['queue_sum'] - ref_means[ep]['waiting']) / ref_means[ep]['waiting'] for ep in ref_means if (fam, init, ep) in by]
        out[init] = float(np.mean(d))
    return out


def compare(a, b):
    """Paired by episode: a, b = episode_means dicts; returns per-endpoint stats with traffic-seed cluster CIs."""
    eps = sorted(set(a) & set(b)); res = {}; seeds = [parse_ep(e)[0] for e in eps]
    for name, _, direction in ENDPOINTS:
        if any(a[e][name] is None or b[e][name] is None for e in eps):
            res[name] = 'MISSING'
            continue
        da = np.array([a[e][name] - b[e][name] for e in eps])
        cl = defaultdict(list)
        for s, v in zip(seeds, da):
            cl[s].append(v)
        cl = {k: np.array(v) for k, v in cl.items()}
        r = dict(mean_diff=float(da.mean()), ci_traffic_seed=boot_cluster(cl), mean_a=float(np.mean([a[e][name] for e in eps])), mean_b=float(np.mean([b[e][name] for e in eps])))
        if name == 'waiting':
            dp = np.array([100 * (a[e][name] - b[e][name]) / b[e][name] for e in eps]); cp = defaultdict(list)
            for s, v in zip(seeds, dp):
                cp[s].append(v)
            cp = {k: np.array(v) for k, v in cp.items()}
            r.update(mean_pct=float(dp.mean()), ci_pct_traffic_seed=boot_cluster(cp), episodes_worse=int((da > 0).sum()), episodes_better=int((da < 0).sum()),
                     episodes=len(eps), _clusters_pct={str(k): v.tolist() for k, v in cp.items()})
        res[name] = r
    return res


def comparisons_for(by, direct, samebyte):
    fams = sorted({k[0] for k in by}); sels = [f for f in fams if f not in ('prefix', 'mp2') and not f.startswith('oracle')]
    E = {f: episode_means(by, f) for f in fams if not f.startswith('oracle')}; out = {}
    if 'mp2' in E:
        out['actor_vs_mp2'] = {'prefix-vs-mp2': compare(E['prefix'], E['mp2'])}
    out['selector_vs_prefix'] = {f'{f}-vs-prefix': dict(compare(E[f], E['prefix']), per_init_waiting_pct=per_init(by, f, E['prefix'])) for f in sels}
    if direct in E:
        out['selector_vs_direct'] = {f'{f}-vs-{direct}': dict(compare(E[f], E[direct]), per_init_waiting_pct=per_init(by, f, E[direct])) for f in sels if f != direct}
    for pair in samebyte:
        bid, ctl = pair.split(':')
        if bid in E and ctl in E:
            out.setdefault('bid_vs_samebyte', {})[f'{bid}-vs-{ctl}'] = compare(E[bid], E[ctl])
    return out


def load_diag(A, name, chk):
    p = A / name
    if not p.exists():
        return 'MISSING'
    d = json.loads(p.read_text()); out = {}
    for k, v in d.items():
        r = v['direct']['dev']
        if not chk(r.get('metric') == 'tie-half pair accuracy (v3)', f'{p}: {k} is a selector diagnostic v3 record (tie-half), not v2 strict'):
            continue
        out[k] = {x: r.get(x) for x in ('realised_gain', 'realised_gain_ci', 'edit_rate', 'harmful_edit_rate', 'oracle_best', 'top1_regret', 'pair_order_accuracy',
                                        'predicted_tie_fraction', 'states')}
    return dict(file=str(p), sha256=sha(p), per_checkpoint=out)


def across(actor_results, section, key):
    vals, clusters = [], []
    for ar in actor_results:
        c = ar['comparisons'].get(section, {}).get(key)
        if not isinstance(c, dict) or not isinstance(c.get('waiting'), dict):
            return None
        vals.append(c['waiting']['mean_pct']); clusters.append({k: np.array(v) for k, v in c['waiting']['_clusters_pct'].items()})
    if not vals:
        return None
    lo = boot_two_level(clusters)
    below = sum(1 for ar in actor_results if ar['comparisons'][section][key]['waiting']['ci_pct_traffic_seed'][1] < 0)
    above = sum(1 for ar in actor_results if ar['comparisons'][section][key]['waiting']['ci_pct_traffic_seed'][0] > 0)
    return dict(actors=len(vals), mean_pct=float(np.mean(vals)), range_pct=[float(min(vals)), float(max(vals))], ci_pct_two_level=lo,
                actors_ci_below_zero=below, actors_ci_above_zero=above, per_actor_pct=vals)


def fmt_ci(c):
    return f'[{c[0]:+.2f}, {c[1]:+.2f}]'


def report(a):
    chk = Check(); actors = []
    for spec in a.actor:
        group, role, d = spec.split(':', 2)
        if role not in ('claim', 'descriptive', 'diagnostic'):
            raise SystemExit(f'role must be claim/descriptive/diagnostic: {spec}')
        actors.append((group, role, Path(d)))
    results = []
    for group, role, A in actors:
        by, info = load_run(A, a.cl, group, a.final, chk)
        results.append(dict(actor=str(A), group=group, role=role, run=info, comparisons=comparisons_for(by, a.direct, a.samebyte),
                            offline_diag={n: load_diag(A, n, chk) for n in a.diag}))
    src = {'scripts/MARL_e3_panel_report.py': sha(Path(__file__))}
    out = dict(reporter='MARL_e3_panel_report.py', closed_loop_subdir=a.cl, final=a.final, status='PASS' if not chk.failed else 'FAIL',
               assertions=chk.log, failed=chk.failed, source_hashes=src, argv=sys.argv[1:])
    lines = []
    if chk.failed:
        lines.append(f'STATUS FAIL: {len(chk.failed)} assertion(s) failed; no comparison is reported.')
        lines += ['  FAIL ' + f for f in chk.failed]
    else:
        out['actors'] = results; out['across_actors'] = {}
        groups = sorted({(r['group'], r['role']) for r in results})
        for g, role in groups:
            R = [r for r in results if r['group'] == g and r['role'] == role]
            for section in ('actor_vs_mp2', 'selector_vs_prefix', 'selector_vs_direct', 'bid_vs_samebyte'):
                keys = sorted(set.intersection(*[set(r['comparisons'].get(section, {})) for r in R])) if R else []
                for key in keys:
                    x = across(R, section, key)
                    if x:
                        out['across_actors'].setdefault(f'{g}:{role}', {}).setdefault(section, {})[key] = x
        lines.append(f'STATUS PASS ({len(chk.log)} assertions). Closed loop {a.cl}; waiting = queue_sum, paired by episode inside each actor; '
                     'CI = traffic-seed cluster bootstrap (both loads together); selector inits averaged within the actor.')
        for r in results:
            inf = r['run']; gt = inf['gates']
            g1 = gt['G1']['pass'] if isinstance(gt['G1'], dict) else 'MISSING'; g2 = gt['G2']['pass'] if isinstance(gt['G2'], dict) else 'MISSING'
            lines.append(f"== {r['actor']}  [{r['group']}, {r['role']}]  recipe {inf['recipe']}  G1 {g1}  G2 {g2}  cap +{inf['cap']}  {inf['capacity']}  "
                         f"seeds {min(inf['traffic_seeds'])}-{max(inf['traffic_seeds'])} x {inf['headways']}")
            for section, cs in r['comparisons'].items():
                for key, c in cs.items():
                    w = c['waiting']
                    gr = ' '.join(f"{n} {c[n]['mean_diff']:+.1f}" if isinstance(c[n], dict) else f'{n} MISSING' for n in
                                  ('finished_vehicles', 'unfinished_vehicles', 'travel_time_censored', 'bytes', 'edits'))
                    pi = c.get('per_init_waiting_pct'); pis = (' inits ' + ' '.join(f'{k} {v:+.2f}' for k, v in pi.items())) if pi else ''
                    lines.append(f"   {section:18s} {key:32s} waiting {w['mean_pct']:+.2f}% {fmt_ci(w['ci_pct_traffic_seed'])} "
                                 f"(abs {w['mean_diff']:+.1f}; worse {w['episodes_worse']}/{w['episodes']}) | {gr}{pis}")
            for n, dg in r['offline_diag'].items():
                if isinstance(dg, dict):
                    for k, v in dg['per_checkpoint'].items():
                        lines.append(f"   offline {n}:{k:24s} dev gain {v['realised_gain']:+.2f} edit {v['edit_rate']:.2f} harm|edit {v['harmful_edit_rate']} "
                                     f"regret {v['top1_regret']:.2f} pair acc (tie-half) {v['pair_order_accuracy']:.3f}")
                else:
                    lines.append(f'   offline {n}: MISSING')
        for gk, secs in out['across_actors'].items():
            for section, ks in secs.items():
                for key, x in ks.items():
                    lines.append(f"ACROSS {gk} ({x['actors']} actors) {section} {key}: waiting {x['mean_pct']:+.2f}% two-level CI {fmt_ci(x['ci_pct_two_level'])} "
                                 f"range {fmt_ci(x['range_pct'])}; actors with CI < 0: {x['actors_ci_below_zero']}, > 0: {x['actors_ci_above_zero']}")
        lines.append('Reading: a CI containing 0 is NOT equivalence; actor_vs_mp2 is competence, not selector evidence; roles other than claim are not method results.')
    for r in out.get('actors', []):                       # drop the internal cluster arrays from the JSON copy only after 'across'
        for cs in r['comparisons'].values():
            for c in cs.values():
                if isinstance(c.get('waiting'), dict):
                    c['waiting']['clusters_pct_by_traffic_seed'] = c['waiting'].pop('_clusters_pct')
    txt = '\n'.join(lines)
    return out, txt


def selftest():
    import tempfile, shutil, copy
    tmp = Path(tempfile.mkdtemp()); A = tmp / 'actor_s0'; C = A / 'cl'; SD = A / 'sel'
    for p in (C, SD, A / 'msguse'):
        p.mkdir(parents=True)
    (A / 'ckpt_best.pt').write_bytes(b'actor'); (A / 'config.json').write_text(json.dumps(dict(seed=0, iters=2000)))
    (A / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', best_select=1300, mp2_select=1730)))
    (A / 'msguse/report.json').write_text(json.dumps(dict(none_vs_actual_pct=dict(mean=5, ci95=[2, 8]), input_action_change_rate=dict(none=0.5))))
    for fam, bid in (('sel_nobid', False), ('sel_bid', True)):
        for s in (0, 1, 2):
            (SD / f'model_{fam}_s{s}.pt').write_bytes(f'{fam}{s}'.encode())
            (SD / f'job_{fam}_s{s}.json').write_text(json.dumps(dict(bid=bid, actor_ckpt=str(A / 'ckpt_best.pt'), results=dict(direct=dict(tau=1.0)))))
    rng = np.random.default_rng(1); rows = []
    for seed in (901, 902, 903, 904):
        for load in (8, 16):
            base = 2000 + 100 * rng.standard_normal()
            for meth, eff, bid in (('prefix', 1.0, False), ('mp2', 1.2, False)) + tuple((f'{f}/s{s}', e, b) for f, e, b in (('sel_nobid', 0.99, False), ('sel_bid', 0.95, True)) for s in (0, 1, 2)):
                q = base * eff; pay = 4800; req = 18
                rows.append(dict(episode=f'seed{seed}_load{load}', method=meth, cap=84, capacity='iid', queue_sum=q, finished=250, bytes=pay + req + (260 if bid else 0),
                                 edits=0 if meth in ('prefix', 'mp2') else 5, summary=dict(decisions=26, finished_vehicles=250, unfinished_vehicles=400, throughput_per_hour=3500,
                                 travel_time_finished_mean=130, travel_time_cityflow_censored=100, payload_bytes=pay, request_bytes=req, revisions=0 if meth in ('prefix', 'mp2') else 50,
                                 clipped_fields=0, access_log=dict(oracle_payloads=0), oracle_access_used=False)))
    good = copy.deepcopy(rows)
    man = dict(status='COMPLETE', args=dict(actor=str(A / 'ckpt_best.pt'), selectors=str(SD), traffic_seeds=[901, 902, 903, 904], headways=[8.0, 16.0], cap=84, capacity='iid'))

    def run(rs, mn=man, final=False, group='scratch'):
        (C / 'rows.json').write_text(json.dumps(rs)); (C / 'manifest.json').write_text(json.dumps(mn)); _H.clear()
        ns = argparse.Namespace(actor=[f'{group}:claim:{A}'], cl='cl', direct='sel_nobid', samebyte=[], diag=[], final=final)
        return report(ns)[0]

    r0 = np.random.default_rng(7); cl = {k: r0.standard_normal(r0.integers(1, 4)) for k in range(6)}
    ref = []; rr = np.random.default_rng(3); K = sorted(cl)
    for _ in range(4000):
        ref.append(np.mean(np.concatenate([cl[K[i]] for i in rr.integers(0, len(K), len(K))])))
    v = _cluster_means(cl, 4000, np.random.default_rng(4))
    assert abs(np.mean(v) - np.mean(ref)) < 0.03 and abs(np.std(v) - np.std(ref)) < 0.03, 'vectorised cluster bootstrap disagrees with the loop'
    const = [{0: np.full(2, 3.0), 1: np.full(2, 3.0)}, {0: np.full(2, 5.0)}]
    assert np.allclose(boot_two_level(const, B=500), [3.0, 5.0]), 'two-level bootstrap range wrong'
    o = run(good); assert o['status'] == 'PASS', o['failed']
    w = o['actors'][0]['comparisons']['selector_vs_prefix']['sel_bid-vs-prefix']['waiting']
    assert abs(w['mean_pct'] - (-5.0)) < 1e-9 and w['ci_pct_traffic_seed'][1] < 0, w
    w2 = o['actors'][0]['comparisons']['actor_vs_mp2']['prefix-vs-mp2']['waiting']
    assert abs(w2['mean_pct'] - 100 * (1 / 1.2 - 1)) < 1e-9, w2
    def must_fail(o, what, sub):
        assert o['status'] == 'FAIL' and any(sub in f for f in o['failed']), f'self-test: {what} was not caught by "{sub}": {o["failed"]}'
    breaks = {
        'duplicate row': (lambda r: r + [copy.deepcopy(r[0])], 'no duplicate'),
        'missing episode': (lambda r: [x for x in r if not (x['method'] == 'sel_bid/s1' and x['episode'] == 'seed903_load8')], 'sel_bid/s1 covers exactly'),
        'wrong cap': (lambda r: [dict(x, cap=56) if i == 5 else x for i, x in enumerate(r)], 'one cap per run'),
        'bytes identity': (lambda r: [dict(x, bytes=x['bytes'] + 1) if x['method'] == 'sel_bid/s0' else x for x in r], 'charged bytes'),
        'unbilled bid': (lambda r: [dict(x, bytes=x['bytes'] - 260) if x['method'] == 'sel_bid/s2' else x for x in r], 'charged bytes'),
        'prefix edits': (lambda r: [dict(x, edits=1) if x['method'] == 'prefix' else x for x in r], 'prefix and mp2 make no edits'),
        'oracle access': (lambda r: [dict(x, summary=dict(x['summary'], oracle_access_used=True)) if x['method'] == 'sel_nobid/s2' else x for x in r], 'zero oracle access'),
    }
    for name, (f, sub) in breaks.items():
        must_fail(run(f(copy.deepcopy(good))), name, sub)
    tr = [dict(x, episode=x['episode'].replace('seed90', 'seed130')) for x in copy.deepcopy(good)]
    must_fail(run(tr, dict(man, args=dict(man['args'], traffic_seeds=[1301, 1302, 1303, 1304]))), 'test seeds', 'reserved test seed')
    assert run(tr, dict(man, args=dict(man['args'], traffic_seeds=[1301, 1302, 1303, 1304])), final=True)['status'] == 'PASS', '--final must admit the test seeds'
    must_fail(run(good, group='bc'), 'wrong recipe', 'declared group')
    must_fail(run(good, dict(man, status='PARTIAL')), 'incomplete run', 'manifest COMPLETE')
    j = SD / 'job_sel_bid_s0.json'; jj = json.loads(j.read_text()); j.write_text(json.dumps(dict(jj, actor_ckpt='/elsewhere/ckpt_best.pt')))
    must_fail(run(good), 'foreign selector', 'trained on labels of')
    j.write_text(json.dumps(jj)); assert run(good)['status'] == 'PASS'
    shutil.rmtree(tmp)
    print('selftest PASS (known -5% effect recovered; duplicate, missing episode, cap, bytes, unbilled bid, prefix edits, oracle access, test seeds, recipe, '
          'incomplete run and foreign-selector breaks each fail their own check)', flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', action='append', default=[], help='group:role:dir, group in scratch/bc/mix/warm, role in claim/descriptive/diagnostic')
    p.add_argument('--cl', default='cl_v3_direct'); p.add_argument('--direct', default='sel_nobid')
    p.add_argument('--samebyte', action='append', default=[], help='BID:CONTROL recipe names in the same run')
    p.add_argument('--diag', action='append', default=[], help='selector diagnostic v3 JSON name inside each actor dir')
    p.add_argument('--final', action='store_true', help='allow the reserved test seeds (only after the dated FROZEN protocol)')
    p.add_argument('--selftest', action='store_true'); p.add_argument('--out'); p.add_argument('--out-txt')
    a = p.parse_args()
    selftest()
    if a.selftest:
        return
    if not a.actor or not a.out:
        p.error('--actor and --out are required')
    out, txt = report(a)
    Path(a.out).write_text(json.dumps(out, indent=1, default=float))
    if a.out_txt:
        Path(a.out_txt).write_text(txt + '\n')
    print(txt, flush=True)
    sys.exit(0 if out['status'] == 'PASS' else 2)


if __name__ == '__main__':
    main()
