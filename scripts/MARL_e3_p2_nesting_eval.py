#!/usr/bin/env python3
"""P2 nesting panel evaluator (03/10/2026 18:4x EDT; PROTOCOL_E3_P2_NESTING_20261003.md).  One process = one receiver checkpoint;
arms channel/arm in {K1, U1, U2} x {PLAIN, EXACT} as listed by --arms, on the same episodes.  The episode loop, the
order-preserving scheduler (NestedDelivery) and the receiver-side exact emulator (Exact) are those of
scripts/MARL_e3_p2_nesting_replay.py (imported).  SELF-CHECK (no manifest otherwise): when both K1/PLAIN and U2/EXACT are run,
U2/EXACT is locked step by step to K1/PLAIN on EVERY episode (packet sets, view entries, encoded inputs, actions, queue);
U2 nests K1 at every step (asserted inside the loop); source hashes unchanged.  --z-only: Z (delivery none) on every episode."""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_actor_train import Scenarios
import scripts.MARL_e3_p2_nesting_replay as NR
import scripts.MARL_e3_fallback_eval_v2 as FB2

SOURCES = NR.SOURCES + ['scripts/MARL_e3_p2_nesting_eval.py']


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    book = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(out); t0 = time.perf_counter(); rows = []; locked = 0
    if a.z_only:
        ckz = torch.load(Path(a.z), weights_only=False)
        for s in a.traffic_seeds:
            for h in a.headways:
                rows.append(dict(arm='Z', episode=f'seed{s}_load{h:g}', queue_sum=FB2.run_z(sc, s, h, ckz)))
        man = dict(mode='z_only', z_sha256=sha(a.z))
    else:
        ck = torch.load(Path(a.relay), weights_only=False)
        for s in a.traffic_seeds:
            for h in a.headways:
                ep = f'seed{s}_load{h:g}'; ref = None
                for arm in a.arms:
                    chan, kind = arm.split('/')
                    lock = iter(ref) if (arm == 'U2/EXACT' and ref is not None) else None
                    q, recs, st = NR.episode(sc, s, h, ck, book, chan, kind, lock=lock, strict=not a.record_lock); info = NR.episode.info
                    if arm == 'K1/PLAIN':
                        ref = recs
                    if lock is not None:
                        locked += 1
                    r = dict(arm=arm, receiver=a.tag, episode=ep, queue_sum=q, delivered=info['delivered'], seconds=info['seconds'],
                             buffer=info['buffer'], locked_to_K1=lock is not None, lock_mismatch_steps=info['lock_mismatch_steps'], first_mismatch=info['first_mismatch'])
                    if st is not None:
                        r.update(entries=st[0], missing=st[1], older_substitute=st[2])
                    rows.append(r)
                if 'U2/EXACT' in a.arms and 'K1/PLAIN' in a.arms:
                    qk = next(r['queue_sum'] for r in rows if r['episode'] == ep and r['arm'] == 'K1/PLAIN')
                    qe = next(r['queue_sum'] for r in rows if r['episode'] == ep and r['arm'] == 'U2/EXACT')
                    if qk != qe and not a.record_lock:
                        raise SystemExit(f'SELF-CHECK FAIL: {ep} U2/EXACT {qe} != K1/PLAIN {qk}')
                    if a.record_lock:
                        next(r for r in rows if r['episode'] == ep and r['arm'] == 'U2/EXACT')['equal_to_K1'] = qk == qe
            print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['arm']} {r['queue_sum']:.0f}" for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}'), flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
        man = dict(mode='eval', relay_sha256=sha(a.relay), arms=a.arms, locked_episodes=locked)
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    man.update(status='COMPLETE', self_check='PASS', args=vars(a), source_hashes=h0, seconds=time.perf_counter() - t0)
    (out / 'manifest.json').write_text(json.dumps(man, indent=1, default=str)); print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay'); p.add_argument('--z'); p.add_argument('--tag', default=''); p.add_argument('--z-only', action='store_true')
    p.add_argument('--arms', nargs='+', default=['K1/PLAIN', 'U1/PLAIN', 'U2/PLAIN', 'U2/EXACT', 'U1/EXACT'])
    p.add_argument('--record-lock', action='store_true', help='Amendment 1: record U2/EXACT vs K1 mismatches instead of aborting')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
