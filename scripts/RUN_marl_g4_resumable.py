#!/usr/bin/env python3
"""Optimised, resumable 4x4 chain (PROTOCOL_E3_G4_RELAUNCH_20261002.md; user 02/10 01:0x "tối ưu nó trc khi chạy").
One dependency-aware job scheduler replaces the five fixed lanes of RUN_marl_g4_replication.sh and the serial downstream chain
(repair pass -> R5 dev -> margin -> reports -> const-K target):
  T<s>   teacher set_full_s<s> (MARL_e3_actor_train_delivery_v6.py, recipe unchanged) via run_with_watchdog WITHOUT --out, so a
         hang resumes IN PLACE from state_last.pt (set_full_s5 / s7 / s9 continue from 1744 / 371 / 323);
  Z<s>   zero-byte student distill_none_s<s> and
  R<s>   relay student relayCage_st_s<s> with the exact-resume trainer v9 (bit-identical to the chain's trainers on the 4x4
         wrappers, TEST_marl_g4_students_v9 PASS, L-253), --park-if-no-state, watchdog without --out;
  EV<s>  the replication evaluations (scripts/RUN_marl_g4_seed_evals.sh, verbatim commands), after Z<s> and R<s>;
  MG<s>  the teacher-margin probe (RUN_marl_g4_margin.sh's command), after EV<s>;
  CK<s>  the const-K development probes and target panel 3301-3364 (scripts/RUN_marl_g4_constk_seed.sh, verbatim), after EV<s>.
Core budget: trainers weigh 2 cores (--threads 2), evaluation jobs 1; at most --cores in use (default 9 of 10, one left for
the system).  Ready jobs start in a fixed priority order: evaluations first (short, they finish seeds), then the work
that completes seeds soonest (seeds 1, 3, 4, 5, 7, 9, 2, 6, 8).  A failed job is retried once (a teacher killed before its
first state is parked to legacy/ first); a second failure excludes it and everything that depends on it (named in the log;
the protocols' completeness rules then apply).  Nothing is deleted.  When no job can run, the reports run once:
MARL_e3_g4_replication_report.py, MARL_e3_g4_r5_report.py, MARL_e3_g4_constk_report.py.
Usage: python -u scripts/RUN_marl_g4_resumable.py [--cores 9] [--dry-run]"""
from __future__ import annotations
import argparse, json, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PY = 'external_envs/runtime/bin/python'
A = 'research/marl_budget/e3_grid4x4_20260930/actors'; E = 'research/marl_budget/e3_g4_replication_20261001'
P = 'research/marl_budget/e3_g4_constk_20261001'; LOGD = 'research/marl_budget/g4_relaunch_20261002'
W = ['scripts/MARL_grid_wrapper.py', '--rows', '4', '--cols', '4', '--']
WR = ['scripts/MARL_grid_relay_wrapper.py', '--rows', '4', '--cols', '4', '--relay-slots', 'nearest8', '--']
TR = '--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 --set-actor'.split()
ORDER = [1, 3, 4, 5, 7, 9, 2, 6, 8, 0]
ENV = {'CIG_EXTERNAL_RUNTIME_ACTIVE': '1', 'PYTHONDONTWRITEBYTECODE': '1', 'OMP_NUM_THREADS': '1'}


def done(rel):
    return (ROOT / rel / 'manifest.json').exists()


def wd(log, extra=()):
    return [PY, 'scripts/run_with_watchdog.py', '--log', log, *extra]


def jobs():
    J = {}
    for s in range(10):
        J[f'T{s}'] = dict(cores=2, deps=[], out=f'{A}/set_full_s{s}', kind='teacher',
                          cmd=wd(f'{A}/set_full_s{s}.log', ['--stall', '1200', '--retries', '20']) + ['--', PY, '-u', *W,
                              'scripts/MARL_e3_actor_train_delivery_v6.py', '--seed', str(s), *TR, '--delivery', 'full', '--out', f'{A}/set_full_s{s}'])
        J[f'Z{s}'] = dict(cores=2, deps=[f'T{s}'], out=f'{A}/distill_none_s{s}', kind='student',
                          cmd=wd(f'{A}/distill_none_s{s}.log', ['--stall', '1200', '--retries', '20']) + ['--', PY, '-u', *W,
                              'scripts/MARL_e3_actor_distill_v9.py', '--teacher', f'{A}/set_full_s{s}/ckpt_best.pt', '--student-delivery', 'none',
                              '--seed', str(s), '--iters', '500', '--threads', '2', '--park-if-no-state', '--out', f'{A}/distill_none_s{s}'])
        J[f'R{s}'] = dict(cores=2, deps=[f'T{s}'], out=f'{A}/relayCage_st_s{s}', kind='student',
                          cmd=wd(f'{A}/relayCage_st_s{s}.log', ['--stall', '1200', '--retries', '20']) + ['--', PY, '-u', *WR,
                              'scripts/MARL_e3_actor_distill_v9.py', '--teacher', f'{A}/set_full_s{s}/ckpt_best.pt', '--student-delivery', 'prefix',
                              '--relay', 'age', '--seed', str(s), '--iters', '500', '--quant', '4', '--order', 'agefirst', '--park-if-no-state',
                              '--out', f'{A}/relayCage_st_s{s}'])
        J[f'EV{s}'] = dict(cores=1, deps=[f'Z{s}', f'R{s}'], kind='eval', outs=[f'{E}/{t}' for t in (f'Rdev_s{s}_low', f'VD_s{s}', f'Z_s{s}', f'R_s{s}_iid', f'R_s{s}_low')],
                           cmd=['bash', 'scripts/RUN_marl_g4_seed_evals.sh', str(s)])
        J[f'MG{s}'] = dict(cores=1, deps=[f'EV{s}'], kind='eval', outs=[f'{E}/MG_s{s}'],
                           cmd=wd(f'{E}/MG_s{s}.log', ['--out', f'{E}/MG_s{s}', '--stall', '900', '--retries', '3']) + ['--', PY, '-u', *WR,
                               'scripts/MARL_e3_teacher_margin_probe.py', '--relay', f'{A}/relayCage_st_s{s}/ckpt_best.pt', '--teacher',
                               f'{A}/set_full_s{s}/ckpt_best.pt', '--parity', f'{E}/Rdev_s{s}_low/rows.json', '--out', f'{E}/MG_s{s}'])
        ck = ([f'Zdev_s{s}'] + [f'NF_s{s}_{c}' for c in ('const1', 'const2', 'const3', 'iid', 'low')] + [f'VS_s{s}_K{K}' for K in (1, 2, 3, 0)]
              + [f'NF3_s{s}_K{K}' for K in (1, 2, 3, 0)] + [f'Z_s{s}'] + [f'R_s{s}_K{K}_A-1' for K in (1, 2, 3, 0)] + [f'R_s{s}_K1_clip'])
        J[f'CK{s}'] = dict(cores=1, deps=[f'EV{s}'], kind='eval', outs=[f'{P}/{t}' for t in ck], cmd=['bash', 'scripts/RUN_marl_g4_constk_seed.sh', str(s)])
    return J


def complete(j):
    return done(j['out']) if 'out' in j else all(done(o) for o in j['outs'])


def priority(name):
    kind = name.rstrip('0123456789'); s = int(name[len(kind):])
    k = {'EV': 0, 'MG': 1, 'CK': 2, 'Z': 3, 'R': 3, 'T': 4}[kind]
    return (0 if k <= 2 else 1, ORDER.index(s), k)


def log(f, msg):
    line = f'{time.strftime("%a %b %d %H:%M:%S %Z %Y")} {msg}'; print(line, flush=True); f.write(line + '\n'); f.flush()


def free_gb():
    return shutil.disk_usage('/System/Volumes/Data').free / 2 ** 30


def dedupe(f):
    log(f, f'DEDUPE start ({free_gb():.1f} GB free)')
    p = subprocess.run([PY, '-u', 'scripts/UTIL_dedupe_hardlink.py', '--log', 'research/marl_budget/dedupe_hardlink_20261002.jsonl',
                        'research/marl_budget', 'legacy'], cwd=ROOT, env={**__import__('os').environ, **ENV}, capture_output=True, text=True)
    log(f, f'DEDUPE rc={p.returncode} {p.stdout.strip().splitlines()[-1] if p.stdout.strip() else p.stderr[-200:]} ({free_gb():.1f} GB free)')


def main(a):
    J = jobs(); logd = ROOT / LOGD
    state = {n: ('done' if complete(j) else 'todo') for n, j in J.items()}; tries = {n: 0 for n in J}; run = {}
    if a.dry_run:
        print('complete:', sorted(n for n, v in state.items() if v == 'done'))
        for n in sorted((n for n in J if state[n] == 'todo'), key=priority):
            print(n, J[n]['cores'], J[n]['deps'], ' '.join(J[n]['cmd'])[:220])
        return
    logd.mkdir(parents=True, exist_ok=True); f = open(logd / 'scheduler.log', 'a')
    log(f, f'START cores={a.cores}; complete: {sorted(n for n, v in state.items() if v == "done")}')
    last_dedupe = 0.0
    while True:
        if free_gb() < 25 and time.time() - last_dedupe > 3600:     # hard links only, finished runs only (L-255)
            dedupe(f); last_dedupe = time.time()
        for n, p in list(run.items()):
            rc = p.poll()
            if rc is None:
                continue
            del run[n]; ok = complete(J[n])
            if ok:
                state[n] = 'done'; log(f, f'DONE {n} rc={rc}')
            elif tries[n] < 2:
                state[n] = 'todo'; log(f, f'RETRY-LATER {n} rc={rc} (attempt {tries[n]} failed)')
            else:
                state[n] = 'failed'; log(f, f'FAILED {n} rc={rc} after {tries[n]} attempts')
        for n in J:                                             # exclude what depends on a failure
            if state[n] == 'todo' and any(state[d] in ('failed', 'excluded') for d in J[n]['deps']):
                state[n] = 'excluded'; log(f, f'EXCLUDED {n} (dependency failed)')
        used = sum(J[n]['cores'] for n in run)
        ready = sorted((n for n in J if state[n] == 'todo' and all(state[d] == 'done' for d in J[n]['deps'])), key=priority)
        blocked = False
        for n in ready:
            j = J[n]
            if used + j['cores'] > a.cores:
                continue
            if free_gb() < 15:
                if time.time() - last_dedupe > 1800:
                    dedupe(f); last_dedupe = time.time()
                if free_gb() < 15:
                    log(f, f'DISK LOW ({free_gb():.1f} GB): not starting {n}; waiting'); blocked = True; break
            if j.get('kind') == 'teacher':                      # killed before its first state: park it (never delete)
                o = ROOT / j['out']
                if o.exists() and not (o / 'manifest.json').exists() and not (o / 'state_last.pt').exists():
                    dst = ROOT / 'legacy' / f'g4relaunch_{o.name}_nostate_{time.strftime("%Y%m%d_%H%M%S")}'; o.rename(dst); log(f, f'PARKED {o} -> {dst}')
            tries[n] += 1; state[n] = 'running'
            out = open(logd / f'{n}.log', 'a')
            run[n] = subprocess.Popen(['caffeinate', '-i', *j['cmd']], cwd=ROOT, env={**__import__('os').environ, **ENV}, stdout=out, stderr=subprocess.STDOUT)
            used += j['cores']; log(f, f'START {n} (attempt {tries[n]}, cores {j["cores"]}, in use {used}/{a.cores}) pid {run[n].pid}')
        if not run and not blocked:
            break
        time.sleep(300 if blocked and not run else 30)
    summary = {k: sorted(n for n, v in state.items() if v == k) for k in ('done', 'failed', 'excluded', 'todo')}
    log(f, 'ALL JOBS SETTLED ' + json.dumps(summary))
    (logd / 'summary.json').write_text(json.dumps(summary, indent=1))
    for r in ('MARL_e3_g4_replication_report.py', 'MARL_e3_g4_r5_report.py', 'MARL_e3_g4_constk_report.py'):
        p = subprocess.run([PY, f'scripts/{r}'], cwd=ROOT, env={**__import__('os').environ, **ENV}, capture_output=True, text=True)
        (logd / f'{r}.txt').write_text(p.stdout + p.stderr); log(f, f'REPORT {r} rc={p.returncode}')
    log(f, 'END')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--cores', type=int, default=9); ap.add_argument('--dry-run', action='store_true')
    main(ap.parse_args())
