#!/usr/bin/env python3
"""Render existing phase-boundary evidence; no experiments are rerun."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import ndtr
from matplotlib.ticker import NullFormatter

root=Path(__file__).resolve().parents[1]
folder=root/'research/d6_phase_boundary_20260908'
phase=json.loads((folder/'phase_cost.json').read_text())
risk=json.loads((folder/'local_allocation_risk.json').read_text())
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,3,figsize=(15,4.8),layout='constrained')
a=axes[0]; p=next(p for p in risk['parameters'] if p['q']==4)
rows=sorted([r for r in risk['rows'] if r['q']==4 and r['epsilon']==1e-5],key=lambda r:r['N'])
x=np.linspace(0,2,200);a.plot(x,ndtr(-x),color='#142e54',lw=2,label=r'$\Phi(-q\varepsilon\sqrt{N})$')
xx=[np.sqrt(r['scaled_budget_actual']) for r in rows]
a.vlines(xx,[r['global_allocation_risk_lower']/(p['slope_jump']*r['epsilon']) for r in rows],
                  [r['exact_achievable_worst_risk']/(p['slope_jump']*r['epsilon']) for r in rows],color='#60a5fa',lw=5,alpha=.7,label='Lower–upper interval')
a.errorbar(xx,[r['empirical'][1]['mean_regret']/(p['slope_jump']*r['epsilon']) for r in rows],
 yerr=[1.96*r['empirical'][1]['se_mean_regret']/(p['slope_jump']*r['epsilon']) for r in rows],
 fmt='o',ms=5,color='#ea580c',capsize=3,label='Monte Carlo ±1.96 SE')
a.set(xlabel=r'$q\varepsilon\sqrt{N}$',ylabel=r'Allocation regret / $(J_q\varepsilon)$',title='Local allocation learning: matching risk')
a.text(.98,.95,r'$m=10,\ \varepsilon=10^{-5}$',ha='right',va='top',transform=a.transAxes)
a.legend(fontsize=8);a.grid(alpha=.15)

a=axes[1]
rows=sorted([r for r in phase['phase_trials'] if r['alpha']==.01 and r['side']==1],key=lambda r:r['epsilon'])
xx=np.array([r['epsilon'] for r in rows]);yy=np.array([r['mean_samples'] for r in rows])
a.loglog(xx,yy,'o-',color='#142e54',label='Uniform sign test, mean N')
a.loglog(xx,[r['full_sign_information_lower'] for r in rows],'--',color='#ea580c',label='Information lower bound')
a.set(xlabel=r'Distance to boundary $\varepsilon$',ylabel='Measurement count',title='Exact phase identification gets expensive')
a.text(.02,.03,r'$m=10,\ \alpha=0.01$; 5,000 trials / point',transform=a.transAxes,fontsize=8)
a.set_xticks([.000125,.0005,.002,.008],['0.000125','0.0005','0.002','0.008'])
a.xaxis.set_minor_formatter(NullFormatter())
a.legend(fontsize=8);a.grid(alpha=.15,which='both')

a=axes[2]
for q,color in [(3,'#142e54'),(4,'#ea580c'),(5,'#0f766e')]:
 rows=sorted([r for r in risk['rows'] if r['q']==q and abs(r['scaled_budget_actual']-1)<.01],key=lambda r:r['epsilon'])
 xx=[r['epsilon'] for r in rows]
 a.semilogx(xx,[r['upper_over_leading'] for r in rows],'-o',color=color,ms=4,label=f'm={2*(q+1)} upper')
 a.semilogx(xx,[r['lower_over_leading'] for r in rows],'--',color=color,label=f'm={2*(q+1)} lower')
a.axhline(1,color='gray',lw=1)
a.set(xlabel=r'$\varepsilon$',ylabel=r'Bound / $[J_q\varepsilon\Phi(-1)]$',title='Bounds converge to the same constant')
a.legend(fontsize=8,ncol=2);a.grid(alpha=.15)
fig.suptitle('D6 allocation boundary — known A, unit-cost variance-one Gaussian queries',fontsize=14)
fig.savefig(folder/'phase_boundary_evidence.png',dpi=190)
fig.savefig(folder/'phase_boundary_evidence.pdf')
print(folder/'phase_boundary_evidence.png')
