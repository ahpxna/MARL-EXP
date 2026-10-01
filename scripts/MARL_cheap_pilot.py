#!/usr/bin/env python3
"""Cheap test 2: learn selectors on fixed-actor broadcast tables, held-out episodes.

Same complete TRAIN labels for all methods; no oracle feature enters any network.
This is OFFLINE selector screening on frozen MP2 with held-phase value labels.
It is not actor training, online performance, a latency advantage, or an
acquisition-efficiency experiment. The direct budget-conditioned policy is trained
against expected subset value, not an arbitrary tie-broken optimal subset label.
"""
from __future__ import annotations
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import numpy as np
import torch
from torch import nn
from models.marl_revision_selector import reachable_sets
from models.marl_screening import mask_of, layer_masks


def load_dataset(folder):
    folder=Path(folder)
    manifest=json.loads((folder/'manifest.json').read_text())
    if manifest.get('status')!='COMPLETE': raise ValueError('dataset collection is not COMPLETE')
    path=folder/'tables.jsonl.gz'
    if hashlib.sha256(path.read_bytes()).hexdigest()!=manifest['table_sha256']:
        raise ValueError('dataset table hash mismatch')
    with gzip.open(path,'rt') as f: rows=[json.loads(line) for line in f]
    if len(rows)!=manifest['records'] or not rows: raise ValueError('record count mismatch')
    splits={'train':[],'val':[],'test':[]}; ids={}; seen=set()
    m=rows[0]['m']; d=len(rows[0]['features'])
    for i,r in enumerate(rows):
        if r['m']!=m or len(r['features'])!=d or len(r['values'])!=1<<m:
            raise ValueError('inconsistent context or table size')
        if r['split'] not in splits: raise ValueError('invalid split')
        if ids.setdefault(r['traffic_seed'],r['split'])!=r['split']:
            raise ValueError('same traffic seed occurs in different data splits')
        key=(r['episode_id'],r['t'])
        if key in seen: raise ValueError('duplicate episode/snapshot')
        seen.add(key); splits[r['split']].append(i)
        if r['live_access_before']!=r['live_access_after']:
            raise ValueError('dataset contains live oracle access')
    if not all(splits.values()): raise ValueError('need disjoint train/val/test episodes')
    return manifest,rows,splits


class SelectorNet(nn.Module):
    def __init__(self,d,m,kind,hidden=64):
        super().__init__(); self.kind=kind
        self.encoder=nn.Sequential(nn.Linear(d,hidden),nn.ReLU(),nn.Linear(hidden,hidden),nn.ReLU())
        if kind=='score': self.head=nn.Linear(hidden,m)
        else:
            self.extra=nn.Linear(m if kind=='value' else 1,hidden,bias=False)
            self.head=nn.Sequential(nn.Tanh(),nn.Linear(hidden,1 if kind=='value' else m))

    def forward(self,x,extra=None):
        h=self.encoder(x)
        if self.kind=='score': return self.head(h)
        out=self.head(h[:,None,:]+self.extra(extra)[None,:,:])
        return out.squeeze(-1) if self.kind=='value' else out


def masks_from_logits(logits,k):
    # Stable tie-break by item ID; no dependence on f or hidden state.
    order=np.argsort(-logits,axis=-1,kind='stable')
    return np.sum((1 << order[...,:k]),axis=-1,dtype=np.int64)


def learn(X,Y,train,val,m,seed,epochs,hidden):
    torch.manual_seed(seed); rng=np.random.default_rng(seed)
    # Fit BOTH feature normalizer and target scale on train only.
    mean=X[train].mean(0); std=X[train].std(0); std[std<1e-6]=1
    xt=torch.as_tensor((X-mean)/std,dtype=torch.float32)
    delta=Y-Y[:,[0]]
    scale=max(float(delta[train].std()),1.0)
    yt=torch.as_tensor(delta/scale,dtype=torch.float32)
    masks=torch.tensor([[(s>>i)&1 for i in range(m)] for s in range(1<<m)],dtype=torch.float32)
    budgets=torch.arange(1,m,dtype=torch.float32)[:,None]/m
    layer_ok=(masks.sum(1)[None,:]==torch.arange(1,m)[:,None])
    networks={kind:SelectorNet(X.shape[1],m,kind,hidden) for kind in ('score','value','direct')}
    opts={kind:torch.optim.Adam(net.parameters(),lr=0.003) for kind,net in networks.items()}
    best={kind:float('inf') for kind in networks}; saved={}; history=[]
    singleton=torch.tensor([1<<i for i in range(m)])
    start=time.perf_counter()
    for epoch in range(epochs):
        for idx in np.array_split(rng.permutation(train),max(1,(len(train)+7)//8)):
            xb,yb=xt[idx],yt[idx]
            score_loss=((networks['score'](xb)-yb[:,singleton])**2).mean()
            value_loss=((networks['value'](xb,masks)-yb)**2).mean()
            logits=networks['direct'](xb,budgets)
            subset_logits=torch.einsum('bkm,nm->bkn',logits,masks).masked_fill(~layer_ok[None,:,:],-torch.inf)
            probs=subset_logits.softmax(dim=-1)
            # Same complete-table labels as evaluator; handles multiple optimal sets.
            direct_loss=-(probs*yb[:,None,:]).sum(-1).mean()
            for kind,loss in [('score',score_loss),('value',value_loss),('direct',direct_loss)]:
                opts[kind].zero_grad(); loss.backward(); opts[kind].step()
        if epoch%10==0 or epoch==epochs-1:
            with torch.no_grad():
                scores=networks['score'](xt[val])
                values=networks['value'](xt[val],masks)
                direct=networks['direct'](xt[val],budgets).numpy()
                metrics={'score':float(((scores-yt[val][:,singleton])**2).mean()),
                         'value':float(((values-yt[val])**2).mean())}
                losses=[]
                for j,k in enumerate(range(1,m)):
                    selected=masks_from_logits(direct[:,j,:],k)
                    losses.extend(Y[val][:,layer_masks(m,k)].max(1)-Y[val,selected])
                metrics['direct']=float(np.mean(losses))
                for kind,metric in metrics.items():
                    if not np.isfinite(metric): raise RuntimeError('nonfinite validation objective')
                    if metric<best[kind]:
                        best[kind]=metric; saved[kind]=copy.deepcopy(networks[kind].state_dict())
                history.append(dict(epoch=epoch,validation=metrics))
                print(f'seed {seed} epoch {epoch+1}/{epochs}: validation {metrics}',flush=True)
    for kind,net in networks.items(): net.load_state_dict(saved[kind]); net.eval()
    return networks,xt,masks,budgets,dict(mean=mean.tolist(),std=std.tolist(),target_scale=scale,
        validation_history=history,seconds=time.perf_counter()-start)


def evaluate(rows,indices,Y,nets,xt,masks,budgets):
    m=rows[0]['m']; records=[]
    with torch.no_grad():
        w=nets['score'](xt[indices]).numpy()
        fh=nets['value'](xt[indices],masks).numpy()
        direct=nets['direct'](xt[indices],budgets).numpy()
    for z,index in enumerate(indices):
        row=rows[index]; f=Y[index]
        rank=tuple(int(i) for i in np.argsort(-w[z],kind='stable'))
        for j,k in enumerate(range(1,m)):
            layer=layer_masks(m,k); P=mask_of(rank[:k])
            best=float(max(f[layer]))
            cand1=[mask_of(s) for s in reachable_sets(rank,k,1)]
            cand2=[mask_of(s) for s in reachable_sets(rank,k,2)]
            chosen={
                'cached_queue_prefix':mask_of(row['cached_queue_ranking'][:k]),
                'learned_score_prefix':P,
                'learned_repair_R1':max(cand1,key=lambda s:fh[z,s]),
                'learned_repair_R2':max(cand2,key=lambda s:fh[z,s]),
                'direct_budget_network':int(masks_from_logits(direct[z,j,:],k)),
                'critic_unrestricted_search':max(layer,key=lambda s:fh[z,s]),
                'oracle_repair_R1':max(cand1,key=lambda s:f[s]),
                'oracle_per_budget':max(layer,key=lambda s:f[s]),
            }
            for method,selected in chosen.items():
                records.append(dict(episode_id=row['episode_id'],t=row['t'],k=k,method=method,
                    selected_mask=int(selected),value=float(f[selected]),regret=best-float(f[selected]),
                    gain_over_learned_prefix=float(f[selected]-f[P]),
                    oracle_R1_headroom=float(max(f[cand1])-f[P])))
    grouped={}
    for r in records:
        grouped.setdefault((r['method'],r['episode_id']),[]).append(r)
    episode=[]
    for (method,eid),rr in grouped.items():
        episode.append(dict(method=method,episode_id=eid,n_context_budget_pairs=len(rr),
            mean_regret=float(np.mean([r['regret'] for r in rr])),
            mean_gain_over_learned_prefix=float(np.mean([r['gain_over_learned_prefix'] for r in rr])),
            fraction_hurts_prefix=float(np.mean([r['gain_over_learned_prefix'] < -1e-9 for r in rr]))))
    summary={method:dict(mean_episode_regret=float(np.mean([r['mean_regret'] for r in episode if r['method']==method])),
                        mean_episode_gain=float(np.mean([r['mean_gain_over_learned_prefix'] for r in episode if r['method']==method])))
             for method in sorted({r['method'] for r in episode})}
    return records,episode,summary


def main(args):
    if args.epochs<1 or args.hidden<1: raise ValueError('epochs and hidden must be positive')
    torch.set_num_threads(1)
    manifest,rows,splits=load_dataset(args.data)
    if len(set(args.seeds)) != len(args.seeds): raise ValueError('training seeds must be distinct')
    if len(splits['train']) < 32 and not args.allow_tiny:
        raise ValueError('too few training contexts for screening; collect --profile pilot, or use --allow-tiny ONLY for wiring checks')
    out=args.out.resolve(); out.mkdir(parents=True,exist_ok=False)
    X=np.asarray([r['features'] for r in rows],dtype=np.float32)
    Y=np.asarray([r['values'] for r in rows],dtype=np.float64)
    if not np.isfinite(X).all() or not np.isfinite(Y).all(): raise ValueError('nonfinite input')
    sources=[Path(__file__),ROOT/'models/marl_screening.py',ROOT/'models/marl_revision_selector.py']
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    runs=[]
    for seed in args.seeds:
        nets,xt,masks,budgets,training=learn(X,Y,splits['train'],splits['val'],rows[0]['m'],seed,args.epochs,args.hidden)
        records,episodes,summary=evaluate(rows,splits['test'],Y,nets,xt,masks,budgets)
        (out/f'seed_{seed}_test.json').write_text(json.dumps(dict(records=records,episodes=episodes,summary=summary),indent=2))
        torch.save(dict(networks={k:v.state_dict() for k,v in nets.items()},normalization=training,
                        m=rows[0]['m'],input_dim=X.shape[1],hidden=args.hidden),out/f'seed_{seed}.pt')
        runs.append(dict(seed=seed,training=training,summary=summary,
            parameter_counts={k:sum(p.numel() for p in net.parameters()) for k,net in nets.items()}))
    if hashes!={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}:
        raise RuntimeError('training source changed during run')
    result=dict(status='COMPLETE',evidence_class='OFFLINE SELECTOR PILOT; frozen heuristic actor, NOT learned-MARL outcomes',
        limitations=['Full table calibration labels shared by all methods; acquisition advantage not tested',
                     'No online rollouts of the learned selector; test contexts from an exogenous collection policy',
                     'Held-phase short-horizon values, not long-run traffic performance',
                     'No timing/latency advantage or neural confidence guarantee',
                     'Tiny-data override enabled: wiring check only' if args.allow_tiny else 'Small-data screening, not a final benchmark'],
        data=str(args.data.resolve()),data_table_sha256=manifest['table_sha256'],source_hashes=hashes,
        splits={k:dict(records=len(v),episodes=sorted({rows[i]['episode_id'] for i in v})) for k,v in splits.items()},
        config=dict(epochs=args.epochs,hidden=args.hidden,seeds=args.seeds,device='cpu',torch_threads=1),runs=runs)
    (out/'report.json').write_text(json.dumps(result,indent=2,allow_nan=False))
    print(f'COMPLETE: {out}/report.json',flush=True)
    for run in runs: print(json.dumps(dict(seed=run['seed'],test=run['summary']),indent=2),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data',required=True,type=Path); p.add_argument('--out',required=True,type=Path)
    p.add_argument('--allow-tiny',action='store_true',help='wiring checks only; allow fewer than 32 train contexts')
    p.add_argument('--epochs',type=int,default=150); p.add_argument('--hidden',type=int,default=64)
    p.add_argument('--seeds',type=int,nargs='+',default=[0,1,2])
    main(p.parse_args())
