#!/usr/bin/env python3
"""Live progress dashboard for the running E3 jobs (read-only): adds training.html to a watch viewer directory.

The page is served by the same `python3 -m http.server` as the CityFlow replay viewer.  It reads the jobs' OWN log files
through symlinks (nothing is copied, nothing running is touched) and re-reads them every 30 s:
  training   log.jsonl of each actor being trained: train Σ waiting per iteration, greedy select-split Σ waiting at
             every evaluation, the MP2 reference, iteration / target;
  labels     every label shard's watchdog log (all attempts): unique (episode, t) states printed so far against the
             shard's expected count, and any printed failure (fails > 0) or Traceback;
  analyses   the F5b multi-receiver decomposition shards: states done / expected.
Approximate by construction: counts come from the logs, not from the label files (the label audit does that).
"""
from __future__ import annotations
import argparse, json, os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M = ROOT / 'research/marl_budget'
TRAIN = {'scratch s0 (lane 2)': ('e3_scratch_20260928_0043/actor_s0', 2000), 'scratch s4 (lane C)': ('e3_scratch_seeds34_20260928/actor_s4', 2000),
         'mix s3 (F2-C)': ('e3_mixactor_20260928/actor_s3', 2000)}


def shard_eps(n_eps, k, n):
    return len(list(range(n_eps))[k::n])


def label_jobs():
    jobs = []
    D = 'e3_scratch_seeds34_20260928/actor_s3/dense'
    for k in range(6):
        jobs.append((f'dense scratch s3 train_{k}', [f'{D}/labels_train_{k}.log'], shard_eps(128, k, 6) * 19))
    for sp in ('select', 'dev'):
        jobs.append((f'dense scratch s3 {sp}', [f'{D}/labels_{sp}.log'], 16 * 19))
    B4 = 'e3_run_seeds34_20260928/actor_s4'
    for k in range(3):
        jobs.append((f'BC s4 train_{k}', [f'{B4}/labels_train_{k}.log', f'{B4}/labels_train_{k}.v3.log'], shard_eps(128, k, 3) * 6))
    B1 = 'e3_run_20260928_003858/actor_s1'
    for k in range(6):
        jobs.append((f'BC s1 train_{k}', [f'{B1}/labels_train_{k}.log'], shard_eps(128, k, 6) * 6))
    for sp in ('select', 'dev'):
        jobs.append((f'BC s1 {sp}', [f'{B1}/labels_{sp}.log'], 16 * 3))
    return jobs


PAGE = r'''<!doctype html><html><head><meta charset="utf-8"><title>E3 live progress</title>
<style>
:root{--bg:#fafafa;--fg:#1d1d1f;--mut:#6e6e73;--grid:#e3e3e6;--a:#2f6fdf;--b:#d2691e;--c:#3a9d5d;--bad:#c62828;--bar:#dfe7f7}
body{font:14px -apple-system,Helvetica,sans-serif;background:var(--bg);color:var(--fg);margin:16px;max-width:1100px}
h1{font-size:18px;margin:0 0 4px} h2{font-size:15px;margin:22px 0 8px} .mut{color:var(--mut);font-size:12px}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(330px,1fr));gap:12px}
.card{background:#fff;border:1px solid var(--grid);border-radius:8px;padding:10px}
table{border-collapse:collapse;width:100%} td{padding:3px 6px;border-bottom:1px solid var(--grid);font-size:13px;white-space:nowrap}
.barw{background:var(--bar);border-radius:4px;height:10px;width:220px;display:inline-block;vertical-align:middle}
.barf{background:var(--a);height:10px;border-radius:4px} .bad{color:var(--bad);font-weight:600} a{color:var(--a)}
</style></head><body>
<h1>E3 — live progress</h1><div class="mut">Reads the jobs' own logs every 30 s (read-only). <span id="ts"></span> ·
<a href="index.html">CityFlow replays</a></div>
<h2>Actor training (Σ waiting, lower is better)</h2><div class="cards" id="train"></div>
<h2>Continuation labels</h2><div class="card"><table id="labels"></table></div>
<h2>F5b multi-receiver decomposition</h2><div class="card"><table id="f5b"></table></div>
<script>
const CFG = __CFG__;
async function txt(u){try{const r=await fetch(u+'?t='+Date.now());return r.ok?await r.text():''}catch(e){return ''}}
function chart(pts, sel, ref, target){
  const W=320,H=150,P=30; const xs=pts.map(p=>p[0]).concat(sel.map(p=>p[0]),[target]);
  const ys=pts.map(p=>p[1]).concat(sel.map(p=>p[1]),[ref]); if(!ys.length) return '<div class="mut">no data yet</div>';
  const x0=0,x1=Math.max(...xs),y0=Math.min(...ys)*0.95,y1=Math.max(...ys)*1.02;
  const X=x=>P+(W-P-6)*(x-x0)/(x1-x0||1), Y=y=>H-18-(H-28)*(y-y0)/(y1-y0||1);
  const line=(a,c,w)=>a.length?`<polyline fill="none" stroke="${c}" stroke-width="${w}" points="${a.map(p=>X(p[0])+','+Y(p[1])).join(' ')}"/>`:'';
  let s=`<svg width="${W}" height="${H}">`;
  for(let k=0;k<=3;k++){const y=y0+(y1-y0)*k/3; s+=`<line x1="${P}" x2="${W-6}" y1="${Y(y)}" y2="${Y(y)}" stroke="var(--grid)"/><text x="2" y="${Y(y)+4}" font-size="10" fill="var(--mut)">${Math.round(y)}</text>`}
  s+=`<line x1="${P}" x2="${W-6}" y1="${Y(ref)}" y2="${Y(ref)}" stroke="var(--b)" stroke-dasharray="4 3"/>`;
  s+=line(pts,'#b9c8ee',1)+line(sel,'var(--a)',2)+`<text x="${P}" y="${H-3}" font-size="10" fill="var(--mut)">iteration 0 … ${x1}</text></svg>`;
  return s;
}
async function refresh(){
  document.getElementById('ts').textContent='updated '+new Date().toLocaleTimeString();
  let h='';
  for(const [name,[path,target]] of Object.entries(CFG.train)){
    const L=(await txt(path)).trim().split('\n').filter(Boolean).map(l=>{try{return JSON.parse(l)}catch(e){return null}}).filter(Boolean);
    const ref=(L.find(r=>r.ref)||{}).mean_queue_sum||0; const it=L.filter(r=>r.it!==undefined);
    const pts=it.map(r=>[r.it,r.train_queue_sum]); const sel=it.filter(r=>r.select_queue_sum!==undefined).map(r=>[r.it,r.select_queue_sum]);
    const last=it.length?it[it.length-1].it:0, best=sel.length?Math.min(...sel.map(p=>p[1])):null;
    h+=`<div class="card"><b>${name}</b> <span class="mut">iteration ${last} / ${target} · best select ${best===null?'–':Math.round(best)} · MP2 ${Math.round(ref)}</span>
       <div class="barw"><div class="barf" style="width:${Math.min(100,100*last/target)}%"></div></div>${chart(pts,sel,ref,target)}
       <div class="mut">light: train episodes · blue: greedy select split · dashed: MP2</div></div>`;
  }
  document.getElementById('train').innerHTML=h;
  let t='<tr><td><b>shard</b></td><td><b>states (from logs)</b></td><td></td><td><b>fails</b></td></tr>';
  for(const [name,paths,exp] of CFG.labels){
    const keys=new Set(); let fails=0, tb=0;
    for(const p of paths){ for(const l of (await txt(p)).split('\n')){ const m=l.match(/\] (seed\d+_load[\d.]+) t(\d+): .* fails (\d+)$/);
      if(m){keys.add(m[1]+'/'+m[2]); fails=Math.max(fails,+m[3])} if(l.startsWith('Traceback')) tb++; } }
    const done=Math.min(keys.size,exp);
    t+=`<tr><td>${name}</td><td>${keys.size} / ${exp}</td><td><div class="barw"><div class="barf" style="width:${100*done/exp}%"></div></div></td>
        <td class="${fails?'bad':''}">${fails}${tb?' <span class="bad">('+tb+' tracebacks in earlier attempts)</span>':''}</td></tr>`;
  }
  document.getElementById('labels').innerHTML=t;
  let f='<tr><td><b>shard</b></td><td><b>states</b></td><td></td></tr>';
  for(const [name,path,exp] of CFG.f5b){ const n=(await txt(path)).split('\n').filter(l=>/\] seed\d+_load[\d.]+ t\d+: famB/.test(l)).length;
    f+=`<tr><td>${name}</td><td>${n} / ${exp}</td><td><div class="barw"><div class="barf" style="width:${100*Math.min(n,exp)/exp}%"></div></div></td></tr>`; }
  document.getElementById('f5b').innerHTML=f;
}
refresh(); setInterval(refresh, 30000);
</script></body></html>'''


def main(a):
    v = Path(a.viewer); logs = v / 'logs'; logs.mkdir(exist_ok=True); n = 0

    def link(rel):
        nonlocal n
        src = M / rel; dst = logs / rel.replace('/', '__')
        if dst.is_symlink() or dst.exists():
            dst.unlink()
        os.symlink(src, dst); n += 1
        return f'logs/{dst.name}'
    cfg = dict(train={k: [link(f'{p}/log.jsonl'), t] for k, (p, t) in TRAIN.items()},
               labels=[[name, [link(p) for p in paths], exp] for name, paths, exp in label_jobs()],
               f5b=[[f'{a_} shard {k}', link(f'e3_mrdecomp_20260928/{a_}_shard{k}.log'), len(list(range(48))[k::6])] for a_ in ('scratch_s3', 'bc_s3') for k in range(6)])
    (v / 'training.html').write_text(PAGE.replace('__CFG__', json.dumps(cfg)))
    print(f'wrote {v / "training.html"} ({n} log symlinks)')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--viewer', required=True); main(p.parse_args())
