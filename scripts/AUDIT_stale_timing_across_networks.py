# Post-hoc descriptive analysis (15/10/2026, NOVELTY/W21 follow-up): stale-timing harm vs upgrade size across grid4, spider, rand3, Salt Lake.
# Reads saved rows only (git show HEAD: for sparse-checkout paths); no simulation.  Output printed; notes in research/papers/audits/STALE_TIMING_ACROSS_NETWORKS_20261015.md
import json, subprocess, numpy as np
B='research/city_sim/'
def load(p):
    try: d=json.load(open(B+p))
    except FileNotFoundError: d=json.loads(subprocess.run(['git','show','HEAD:'+B+p],capture_output=True,text=True,check=True).stdout)
    assert d['status']=='COMPLETE', p; return {r['seed']:r for r in d['rows']}
def mean(rows,k): return float(np.mean([r[k] for r in rows.values()]))
def pair(a,b,k,pct=False):
    s=sorted(set(a)&set(b)); assert s==sorted(a)==sorted(b),(len(a),len(b))
    return [100*(a[x][k]/b[x][k]-1) if pct else a[x][k]-b[x][k] for x in s]
NET={
 'grid4': dict(ft='spat_pilot_20261004/m2/eval/OFF_FT.json', L=[f'spat_pilot_20261004/m2/eval/OFF_RLH{k}.json' for k in range(4)],
              pairs=[(f'spat_pilot_20261004/m2/eval/{f}_RLH{k}_naive.json', f'spat_pilot_20261004/m2/eval/{f}_RLH{k}_labelled.json') for f in ('F0a','F0b') for k in range(4)],
              spat=[f'spat_pilot_20261004/m2/eval/{f}_RLH{k}_naive_spat.json' for f in ('F0a','F0b') for k in range(4)], ftg=42),
 'spider (1 lane)': dict(ft='m4_20261004/spider/s3/eval/OFF_FT.json', L=['m4_20261004/spider/s3/eval/OFF_RLK11.json','m4_20261004/spider/s3/eval/OFF_RLK111.json'],
              pairs=[(f'm4_20261004/spider/s3/eval/F0_{l}_naive.json', f'm4_20261004/spider/s3/eval/F0_{l}_labelled.json') for l in ('RLK11','RLK111')],
              spat=[f'm4_20261004/spider/s3/eval/F0_{l}_naive_spat.json' for l in ('RLK11','RLK111')], ftg=27),
 'rand3': dict(ft='w8_20261005/net3/dev/FTA.json', L=[f'w8_20261005/net3/dev/LA_t{k}.json' for k in range(21,26)],
              pairs=[(f'w8_20261005/net3/dev/NAIVE_t{k}_s{s}.json', f'w8_20261005/net3/dev/R_t{k}_s{s}.json') for k in range(21,26) for s in (213,313,413,513)], spat=[], ftg=42),
 'Salt Lake 400S': dict(ft='f1_saltlake/gateW/FT_400sX200w.json', L=['f1_saltlake/gateW/RLK11_400sX200w.json','f1_saltlake/gateW/RLK12_400sX200w.json'],
              pairs=[(f'f1_saltlake/tsi/conf/HARM_t11_s{s}.json', f'f1_saltlake/tsi/conf/R_t11_s{s}.json') for s in (13,113)], spat=[], ftg=None),
}
out={}
for n,c in NET.items():
    ft=load(c['ft']); Ls=[load(p) for p in c['L']]
    tl_ft=mean(ft,'timeloss'); g_ft=mean(ft,'green_mean')
    gain=[pair(L,ft,'timeloss') for L in Ls]; gain=float(np.mean([np.mean(g) for g in gain]))
    g_L=float(np.mean([mean(L,'green_mean') for L in Ls])); p90=float(np.mean([mean(L,'green_p90') for L in Ls])); gt50=float(np.mean([mean(L,'green_share_gt50') for L in Ls]))
    fu=[]; ta=[]; th=[]
    for a,b in c['pairs']:
        A,Bb=load(a),load(b); fu+=pair(A,Bb,'fuel_agent',True); ta+=pair(A,Bb,'timeloss_agent'); th+=pair(A,Bb,'timeloss_human')
    sp=[load_raw for load_raw in []]
    vs=[]
    for p in c['spat']:
        try: d=json.load(open(B+p))
        except FileNotFoundError: d=json.loads(subprocess.run(['git','show','HEAD:'+B+p],capture_output=True,text=True).stdout)
        vs.append(d['valid']/d['total'])
    out[n]=dict(tl_ft=tl_ft, gain=gain, gain_pct=100*gain/tl_ft, g_ft=g_ft, g_L=g_L, g_change=100*(g_L/g_ft-1), p90=p90, gt50=gt50,
                harm_fuel=float(np.mean(fu)), harm_fuel_sd=float(np.std(fu)/np.sqrt(len(fu))), harm_tla=float(np.mean(ta)), harm_tlh=float(np.mean(th)), ncells=len(fu), valid=(float(np.mean(vs)) if vs else None),
                n_lights=len(Ls))
    print(n, json.dumps({k:(round(v,3) if isinstance(v,float) else v) for k,v in out[n].items()}))
json.dump(out,open('research/papers/audits/stale_timing_across_networks_20261015.json','w'),indent=1)
