#!/usr/bin/env python3
"""Read-only reanalysis of stored E3 labels/checkpoints and F5 tables. No simulator/training.
Writes only the explicitly requested audit JSON; never modifies producers or results.
"""
import argparse
import collections
import gzip
import hashlib
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import numpy as np
import torch
from scripts.MARL_e3_selector_train import features


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def audit_actor(tag, folder):
    d = ROOT / 'research/marl_budget' / folder / 'actor_s3'
    p = d / 'labels_dev'
    man = json.loads((p / 'manifest.json').read_text())
    states = list(map(json.loads, gzip.open(p / 'labels.jsonl.gz', 'rt')))
    counts = collections.Counter()
    ranges, gains, same_gains, witnesses = [], [], [], []
    for st in states:
        cands = [c for c in st['cands'] if c['bytes'] <= st['b0'] + 74]
        prefix = st['cands'][0]
        assert cands[0] == prefix
        groups = collections.defaultdict(list)
        for c in cands:
            groups[tuple(c['joint'])].append(c)
        state_diff = False
        for joint, group in groups.items():
            if len(group) < 2:
                continue
            counts['duplicate_joint_groups'] += 1
            assert len({c['cont_1'] for c in group}) == 1, 'same joint, different one-step value'
            span = max(c['cont'] for c in group) - min(c['cont'] for c in group)
            if span:
                state_diff = True
                counts['groups_with_different_continuation'] += 1
                ranges.append(span)
                if not witnesses:
                    lo = min(group, key=lambda c: c['cont'])
                    hi = max(group, key=lambda c: c['cont'])
                    witnesses.append(dict(episode=st['episode_id'], t=st['t'], joint=joint,
                        low={k:lo[k] for k in ('sets','bytes','cont','cont_1')},
                        high={k:hi[k] for k in ('sets','bytes','cont','cont_1')}))
        counts['states_with_joint_ambiguity'] += int(state_diff)
        same = [c for c in cands[1:] if c['joint'] == prefix['joint']]
        counts['feasible_nonprefix_candidates'] += len(cands)-1
        counts['same_prefix_joint'] += len(same)
        counts['same_joint_different_cont'] += sum(c['cont'] != prefix['cont'] for c in same)
        counts['same_joint_positive_cont'] += sum(c['cont'] > prefix['cont'] for c in same)
        gains.append(max(c['cont']-prefix['cont'] for c in cands))
        same_gains.append(max([0]+[c['cont']-prefix['cont'] for c in same]))
    ckpath = d / 'selectors_v3/model_legal_bid_resp_s0.pt'
    ck = torch.load(ckpath, weights_only=False)
    mu, sd = ck['cm'], ck['cs']
    blocks = {}
    for name,a,b in [('z',0,109),('K',109,118),('mirror',118,982),('bid',982,len(mu))]:
        sig, mus = sd[a:b], mu[a:b]
        blocks[name] = dict(n=b-a, near_constant=int((sig<1e-5).sum()),
            constant_nonzero=int(((sig<1e-5)&(abs(mus)>1e-3)).sum()),
            empty_cache_abs_z_max=float(np.max(abs(mus/sig))) if name in ('z','mirror') else None)
    vals = np.stack([features(st, True, ck['gap_thr'])[0] for st in states])
    norm = (vals-mu)/sd
    mism = [f for f,h in man['source_hashes'].items() if sha(ROOT/f) != h]
    return dict(actor=tag, states=len(states), cap=84, bid_bytes=10, counts=dict(counts),
        mean_oracle_gain=statistics.mean(gains), mean_same_joint_oracle_gain=statistics.mean(same_gains),
        max_within_joint_cont_range=max(ranges), witnesses=witnesses,
        normalization=dict(checkpoint=str(ckpath.relative_to(ROOT)), blocks=blocks,
            dev_abs_z_max=float(abs(norm).max()), dev_states_over_1000=int((abs(norm)>1000).any(1).sum())),
        source_hash_mismatches=mism, hashes={str(f.relative_to(ROOT)):sha(f) for f in
            (p/'manifest.json',p/'labels.jsonl.gz',ckpath)})


def audit_bridge(tag):
    d = ROOT/'research/marl_budget'/f'e3_bridge_v2_{tag}_s3_20260928'
    tables = json.loads((d/'f.json').read_text()); rows=json.loads((d/'rows.json').read_text())
    errors=[]; top_errors=[]; witnesses=[]
    for r in rows:
        table=tables[f'{r["episode"]}_t{r["t"]}']
        f={frozenset(map(int,k.split(','))) if k else frozenset():v for k,v in table['f'].items()}
        others=table['others']; p=set(r['prefix']); lo={};hi={}
        assert len(f)==2**len(others)
        for j in others:
            delta=[f[a|{j}]-v for a,v in f.items() if j not in a]
            lo[j],hi[j]=min(delta),max(delta)
        eta=max((hi[j]-lo[j])/2 for j in others)
        eta_top=max([eta]+[(hi[q]-lo[i])/2 for i in p for q in others if q not in p])
        w={j:lo[j]+eta_top if j in p else hi[j]-eta_top for j in others}
        violation=max([abs(f[a|{j}]-v-w[j])-eta_top for a,v in f.items() for j in others if j not in a]
            +[w[q]-w[i] for i in p for q in others if q not in p])
        errors.append(abs(eta-r['eta_star']));top_errors.append(abs(eta_top-r['eta_top']));witnesses.append(violation)
    assert max(errors)==max(top_errors)==0
    assert max(witnesses)<=0
    return dict(states=len(rows),max_eta_error=max(errors),max_eta_top_error=max(top_errors),
        explicit_witness_max_violation=max(witnesses),hashes={str(p.relative_to(ROOT)):sha(p) for p in (d/'f.json',d/'rows.json')})


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args()
    torch.set_num_threads(1)
    result=dict(scope='Stored-data diagnostic, not a new experiment or causal attribution',
        actors=[audit_actor('scratch','e3_scratch_seeds34_20260928'),audit_actor('bc','e3_run_seeds34_20260928')],
        bridge={t:audit_bridge(t) for t in ('scratch','bc')},
        self_hash=sha(Path(__file__)))
    Path(a.out).write_text(json.dumps(result,indent=2))
    for r in result['actors']:
        print(r['actor'], 'oracle',r['mean_oracle_gain'],'same-action oracle',r['mean_same_joint_oracle_gain'],
              'empty-cache scale',r['normalization']['blocks']['mirror']['empty_cache_abs_z_max'],
              'source mismatches',r['source_hash_mismatches'])
    print('F5 exact formulas:',result['bridge']['scratch']['max_eta_top_error'],result['bridge']['bc']['max_eta_top_error'])

if __name__=='__main__':main()
