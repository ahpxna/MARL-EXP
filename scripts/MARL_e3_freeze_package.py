#!/usr/bin/env python3
"""E3 F6 freeze package, DRAFT (handoff MARL_REMAINING_WORK_HANDOFF_20260928_1910 W3).  Read-only: hashes, configs,
manifests and logs; no training, no rollouts, and it NEVER writes 'FROZEN'.

Collects everything a freeze must pin, so that the authors' remaining decisions (the method recipe, the endpoint type
and margin, the actor list) are the only OPEN items:
  actors        run of record per seed (e3_scratch_rs_20260928/RUN_OF_RECORD_RULE.md: the first run that completes;
                a lane run that also completes must be identical), ckpt/config sha256, recipe, trainer, G1/G2, role;
  selectors     every candidate recipe present per claim actor: checkpoint sha256, job sha256, saved tau (direct/R1),
                bid bins (gap thresholds), training labels (n_states), loss; normalisation constants are inside the
                checkpoint, so its sha256 pins them;
  comparators   prefix (R = 0), direct no-bid selector, R1, SchedNet-style adaptation, same-byte queue bid, oracle;
  generator     candidate family source (MARL_hetero_pilot_collect.candidates) + its RNG stream rule, N_DEC;
  runtime       closed loop v5 and every source it hashes; the reporter (MARL_e3_panel_report.py);
  bytes         allowance points, bid bytes, the charged-bytes identity the reporter asserts;
  seeds         development panel 901-916, DEV labels 501-508, the reserved test panel 1301-1316 x headways 8/16,
                capacity models (iid; declared shift bursty);
  failures      watchdog attempts / stalls per stage from the logs, legacy/ parked partials;
  statistics    the proposed primary endpoint and the analysis (two-level bootstrap), guardrails;
  open          the decisions that remain the authors'.
Usage: MARL_e3_freeze_package.py --out research/marl_budget/E3_FREEZE_PACKAGE_DRAFT_<stamp>.json
"""
from __future__ import annotations
import argparse, glob, hashlib, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
M = Path('research/marl_budget')
CLAIM = {0: M / 'e3_scratch_rs_20260928/actor_s0', 1: M / 'e3_scratch_rs_20260928/actor_s1', 2: M / 'e3_scratch_rs_20260928/actor_s2',
         3: M / 'e3_scratch_seeds34_20260928/actor_s3', 4: M / 'e3_scratch_rs_20260928/actor_s4'}
LANE = {0: M / 'e3_scratch_20260928_0043/actor_s0', 4: M / 'e3_scratch_seeds34_20260928/actor_s4'}      # the lane runs the replicas replicate
DESCRIPTIVE = {'bc': [M / 'e3_run_20260928_003858/actor_s0', M / 'e3_run_20260928_003858/actor_s1', M / 'e3_run_20260928_003858/actor_s2',
                      M / 'e3_run_seeds34_20260928/actor_s3', M / 'e3_run_seeds34_20260928/actor_s4'],
               'mix': [M / 'e3_mixactor_20260928/actor_s3']}
RUNTIME = 'scripts/MARL_e3_closed_loop_v5.py'


def sha(p):
    p = ROOT / p
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


def jl(p):
    p = ROOT / p
    return json.loads(p.read_text()) if p.exists() else None


def actor_record(A, role):
    from scripts.MARL_e3_panel_report import recipe, gates
    cfg = jl(A / 'config.json') or {}; man = jl(A / 'manifest.json')
    return dict(dir=str(A), role=role, complete=bool(man and man.get('status') == 'COMPLETE'), ckpt=str(A / 'ckpt_best.pt'), ckpt_sha256=sha(A / 'ckpt_best.pt'),
                config_sha256=sha(A / 'config.json'), recipe=recipe(cfg), trainer=cfg.get('trainer', 'MARL_e3_actor_train_v2.py' if 'bc_epochs' in cfg else 'MARL_e3_actor_train.py'),
                seed=cfg.get('seed'), iters=cfg.get('iters'), gates=gates(ROOT / A) if (ROOT / A / 'manifest.json').exists() else 'MISSING',
                training_source_hashes=(man or {}).get('source_hashes'), resumes=(man or {}).get('resumes'))


def selectors_of(A):
    out = {}
    for mf in sorted(glob.glob(str(ROOT / A / 'selectors*/model_*.pt'))):
        mf = Path(mf); jf = mf.with_name(mf.name.replace('model_', 'job_').replace('.pt', '.json')); job = json.loads(jf.read_text()) if jf.exists() else {}
        r = job.get('results', {})
        out[f'{mf.parent.name}/{mf.stem[6:]}'] = dict(model_sha256=hashlib.sha256(mf.read_bytes()).hexdigest(), job_sha256=sha(jf.relative_to(ROOT)) if jf.exists() else None,
                                                    bid=job.get('bid'), resp=job.get('resp'), qbid=job.get('qbid'), priv_joint=job.get('priv_joint'), loss=job.get('loss', 'mse'),
                                                    temperature=job.get('temperature'), tau_direct=(r.get('direct') or {}).get('tau'), tau_R1=(r.get('R1') or {}).get('tau'),
                                                    gap_thresholds=job.get('gap_thresholds'), n_states=job.get('n_states'), actor_ckpt=job.get('actor_ckpt'),
                                                    deployable=not job.get('priv_joint', False), trainer_sources=job.get('source_hashes'))
    return out


def failures(A):
    """Watchdog attempts and stalls per log in an actor dir (a stall is a kill; the log line says STALL either way)."""
    out = {}
    for lg in sorted(glob.glob(str(ROOT / A / '*.log'))) + sorted(glob.glob(str(ROOT / A / 'dense/*.log'))):
        t = Path(lg).read_text(errors='replace'); st = t.count('[watchdog] STALL'); at = len(re.findall(r'\[watchdog\] attempt', t))
        if st or at:
            out[str(Path(lg).relative_to(ROOT))] = dict(stalls=st, retries=at)
    return out


def main(a):
    t0 = time.strftime('%Y-%m-%d %H:%M:%S %Z')
    # run of record per claim seed (rule declared 14:03, before any outcome)
    ror = {}
    for s, A in CLAIM.items():
        lane = LANE.get(s); lane_done = bool(lane and (jl(lane / 'manifest.json') or {}).get('status') == 'COMPLETE')
        rep_done = (jl(A / 'manifest.json') or {}).get('status') == 'COMPLETE'
        if lane_done and rep_done:
            same = sha(lane / 'ckpt_best.pt') == sha(A / 'ckpt_best.pt'); rec = A if same else lane
            why = 'both complete; identical checkpoints' if same else 'both complete; checkpoints differ -> the LANE run is the run of record (rule 2)'
        elif rep_done:
            rec, why = A, ('the replica completed; the lane run did not' if lane else 'the only run of this seed')
        elif lane_done:
            rec, why = lane, 'the lane run completed; the replica did not'
        else:
            rec, why = None, 'NO COMPLETE RUN'
        ror[s] = dict(run_of_record=str(rec) if rec else None, reason=why, lane_run=str(lane) if lane else None, lane_complete=lane_done)
    actors = {f'scratch_s{s}': actor_record(Path(r['run_of_record']), 'claim') for s, r in ror.items() if r['run_of_record']}
    for g, L in DESCRIPTIVE.items():
        for A in L:
            actors[f'{g}_s{(jl(A / "config.json") or {}).get("seed")}'] = actor_record(A, 'descriptive' if g == 'bc' else 'diagnostic (G1 FAIL)')
    for k, v in actors.items():
        if v['recipe'] != k.split('_')[0]:
            raise SystemExit(f'recipe mismatch for {k}: {v["recipe"]}')
    from scripts.MARL_e3_closed_loop_v5 import SOURCES as RT_SOURCES
    from scripts.MARL_e3_selector_train import BID_BYTES, CAP
    pkg = dict(
        status='DRAFT — NOT FROZEN (no FROZEN copy exists; seeds 1301-1316 are closed)', generated=t0, generator=dict(script='scripts/MARL_e3_freeze_package.py', sha256=sha('scripts/MARL_e3_freeze_package.py')),
        protocol_draft=dict(file='research/marl_budget/PROTOCOL_E3_FINAL_DRAFT_20260928.md', sha256=sha('research/marl_budget/PROTOCOL_E3_FINAL_DRAFT_20260928.md')),
        run_of_record=ror, actors=actors,
        selectors={k: selectors_of(Path(v['dir'])) for k, v in actors.items() if v['role'] == 'claim'},
        comparators=dict(
            prefix='committed prefix, R = 0 (runtime method "prefix")',
            direct_nobid='sel_nobid (selectors_v2, direct policy) on the same actor; the price-of-commitment comparator',
            R1='the chosen recipe under policy R1 (ablation; not required to beat direct)',
            schednet_adaptation=dict(note='learned SchedNet-style frozen-actor adaptation (1 B weights); an adaptation, not the original method',
                                     dirs=sorted(str(Path(p).relative_to(ROOT)) for p in glob.glob(str(ROOT / M / 'e3_schednet_v2_20260928/actor*'))),
                                     chain_log_sha256=sha(M / 'e3_schednet_v2_20260928/chain.log'),
                                     OPEN='trained only for scratch s3 (actor0) and BC s3 (actor1); a claim over five actors needs it for every claim actor'),
            samebyte_queue_bid='sb_queuebid (selectors_v4; 10 B own-view queue total), closed loop v5 --qbid; offline only so far',
            oracle='max over the same candidate family with realised continuations: DIAGNOSTIC, never deployable'),
        candidate_generator=dict(source='scripts/MARL_hetero_pilot_collect.py:candidates', sha256=sha('scripts/MARL_hetero_pilot_collect.py'),
                                 rng_stream='np.random.default_rng(80000 + 10*traffic_seed + int(headway)) per episode (closed loop v5 episode())',
                                 decisions_per_episode=26, label_horizon_H=3, family='the prefix plus single-sender swaps per receiver (B1 family), deduplicated'),
        runtime=dict(script=RUNTIME, source_hashes={s: sha(s) for s in RT_SOURCES}, selftest='closed loop v5 --selftest (tau parsing, decision rule) + per-actor self-check '
                     '(runtime scores == trainer path to 1e-5; chosen == trainer dev_chosen) + per-step byte parity', reporter=dict(script='scripts/MARL_e3_panel_report.py',
                     sha256=sha('scripts/MARL_e3_panel_report.py'), selftest='--selftest')),
        bytes=dict(allowance_bytes_per_step=CAP, allowance_points_if_frontier=[28, 56, 84, 140], bid_bytes_per_step=BID_BYTES,
                   rule='per step: charged = the submitted profile cost (<= prefix cost + allowance - bid bytes) + bid bytes; episode total reported for every method',
                   identity_asserted='row bytes == payload + request + 10 x decisions (bid / queue-bid arms), + 0 otherwise', profile_cost_source=sha('models/marl_hetero_selector.py')),
        seeds=dict(actor_training='per protocol (train 128 / select 16 episodes, seeds fixed in the trainer)', label_dev_traffic=list(range(501, 509)),
                   development_closed_loop=list(range(901, 917)), test_reserved=list(range(1301, 1317)), headways=[8, 16], capacity_primary='iid',
                   capacity_declared_shift='bursty (Gilbert-Elliott, MARL_hetero_panel_collect.capacity_trace)'),
        failures={k: failures(Path(v['dir'])) for k, v in actors.items()},
        legacy_parked=sorted(p.name for p in (ROOT / 'legacy').iterdir() if p.is_dir()) if (ROOT / 'legacy').exists() else [],
        statistics=dict(
            primary_proposed='SUPERIORITY of the method over the SAME actor + committed prefix in episode sum of waiting (queue_sum) at +84 B, paired by episode; '
                             'estimate = mean over claim actors of the per-actor mean percent difference (selector inits averaged within an actor); '
                             'two-level bootstrap (actors, then traffic seeds with both headways together), 95%; superiority iff the upper bound < 0',
            secondary=['method vs direct no-bid selector (same cap)', 'method vs same-byte queue bid', 'R1 vs direct', 'per-actor results with traffic-seed CIs',
                       'declared shift: bursty capacities'],
            guardrails=['finished vehicles', 'unfinished vehicles', 'throughput per hour', 'mean travel time of finished trips', 'CityFlow censored travel time',
                        'charged bytes', 'edits', 'revisions', 'clipped fields', 'oracle-access log == 0'],
            reading=['a CI containing 0 is not equivalence', 'actor vs MP2 is competence, not selector evidence', 'no endpoint switch after seeing test data',
                     'non-inferiority or a byte trade-off needs a margin and a test fixed BEFORE the test run']),
        open=[dict(item='the method recipe', rule='chosen on SELECT by decision quality, only among recipes with a development signal (PROTOCOL_E3_FINAL_DRAFT §2)', who='worker proposes from development; authors confirm'),
              dict(item='the primary endpoint TYPE (superiority / non-inferiority with margin / budget stability)', who='authors'),
              dict(item='the actor list of the claim (proposed: every scratch seed 0-4 that passes G1/G2)', who='authors'),
              dict(item='the SchedNet-style comparator for every claim actor', who='worker (compute), once the recipe is fixed'),
              dict(item='whether a frontier (+28/+56/+140) or the bursty shift is claimed', who='authors'),
              dict(item='a dated FROZEN copy with its own sha256', who='authors, after the items above')])
    missing = [s for s, r in ror.items() if not r['run_of_record']]
    pkg['blocking'] = ([f'scratch seed {s}: no complete actor' for s in missing] +
                       [f'{k}: labels / selectors / closed loop not complete' for k, v in actors.items() if v['role'] == 'claim' and not (ROOT / v['dir'] / 'cl_v3_direct/manifest.json').exists()])
    Path(a.out).write_text(json.dumps(pkg, indent=1, default=str))
    def gate(v, g):
        gt = v['gates']
        return gt[g]['pass'] if isinstance(gt, dict) and isinstance(gt.get(g), dict) else 'MISSING'
    claim = [f"{k} ({v['dir']}, G1 {gate(v, 'G1')}, G2 {gate(v, 'G2')})" for k, v in actors.items() if v['role'] == 'claim']
    print('freeze package DRAFT -> ' + a.out, flush=True)
    print('  claim actors: ' + '; '.join(claim), flush=True)
    print('  blocking: ' + str(pkg['blocking']), flush=True)
    print('  open: ' + str([o['item'] for o in pkg['open']]), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True)
    main(p.parse_args())
