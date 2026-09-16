#!/usr/bin/env python3
"""Render display equations as transparent PNGs, typeset rather than typed.

matplotlib's mathtext with the Computer Modern font set gives LaTeX-quality output with
no TeX installation, and a transparent background so the equation sits on the poster's
own colour.  Each equation is written once here and referenced by key from a poster spec.
"""
import argparse, json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

matplotlib.rcParams['mathtext.fontset'] = 'cm'
INK = '#161213'
CRAN = '#63131E'
OUT = Path('research/papers/_figures/eq')

EQUATIONS = {
 # ---------------- MASTER ----------------
 'master_witness':
   r'\theta^{(0)}=(1,\,0,\,0,\,1),\;\; b^{(0)}=(0,\,0)'
   r'\qquad\qquad \lambda=(\frac{1}{4},\,-\frac{3}{4},\,0,\,1),\;\; b^{(1)}=(\frac{3}{4},\,0)',
 'master_dichotomy':
   r'\forall\, i:\;\; \theta^{(0)}_i + b^{(0)}_{g(i)} \;=\; \lambda_i + b^{(1)}_{g(i)}'
   r'\qquad \mathrm{but} \qquad \{\, i:\theta^{(0)}_i>\frac{1}{2}\,\}\;\neq\;\{\, i:\lambda_i>\frac{1}{2}\,\}',
 'master_gamma_zero':
   r'\Longrightarrow\quad \Gamma \;=\; 0',
 'master_profile':
   r'\inf_{t\in\mathbb{R}}\left[\frac{a\,(\Delta-t)^2}{2}+\frac{b\,t^2}{2}\right]'
   r'\;=\;\frac{a\,b\,\Delta^{2}}{2\,(a+b)}\;=\;\frac{\Delta^{2}}{2\left(\frac{1}{a}+\frac{1}{b}\right)}',
 'master_group_lower':
   r'h\,(x+z)\;\leq\;x\,z \qquad\Longrightarrow\qquad h\,(\sqrt{m}+\sqrt{\kappa})^{2}\;\leq\;m\,x+\kappa\,z',
 'master_group_attained':
   r'\frac{z}{x}=\sqrt{\frac{m}{\kappa}}\;\;\mathrm{attains\;it,\;spending\;exactly}\;\;h\,(\sqrt{m}+\sqrt{\kappa})^{2}',
 'master_upper':
   r'\sum_{g}\left(m\,x_g+\kappa\,z_g\right)\leq 1,\quad'
   r'\frac{2V}{\Delta^{2}}\,(x_g+z_g)\leq x_g z_g\;\;\forall g'
   r'\qquad\Longrightarrow\qquad V\;\leq\;\frac{\Delta^{2}}{2K\,(\sqrt{m}+\sqrt{\kappa})^{2}}',
 'master_rate':
   r'\Gamma^{*}\;=\;\frac{\Delta^{2}}{2\,K\,(\sqrt{m}+\sqrt{\kappa})^{2}}',
 'master_limits':
   r'\kappa\to 0:\;\;\Gamma^{*}\to\frac{\Delta^{2}}{2Km}'
   r'\qquad\qquad \kappa\;\mathrm{large}:\;\;\Gamma^{*}\asymp\frac{\Delta^{2}}{2K\kappa}'
   r'\qquad\qquad \mathrm{crossover}\;\;\kappa=m',
 'master_anchor':
   r'U_{0}=\frac{1}{8}\;\;\mathrm{(cap,\;attained)}\qquad<\qquad L_{1}=\frac{261}{1520}\;\;\mathrm{(anchored)}',
 'master_hadamard':
   r'(c_k\,d_k)^{2}\;=\;c_k^{2}\,d_k^{2}\qquad \mathrm{width}\;r\;\longmapsto\;\mathrm{width}\;r^{2}',

 # ---------------- QUERY ----------------
 'query_mixture':
   r'p_{W,h}(y)\;=\;\sum_{x}\pi_x\,\varphi_\sigma\left(y-f_W(x)-h\,g(x)\right)',
 'query_hermite':
   r'\frac{d^{\,n}}{dy^{\,n}}\,e^{-y^{2}/2\sigma^{2}}\;=\;H_n(y)\,e^{-y^{2}/2\sigma^{2}}'
   r'\qquad H_0=1,\quad H_{n+1}=H_n^{\,\prime}-\frac{y}{\sigma^{2}}H_n',
 'query_sumswap':
   r'\left.\partial_h^{\,j}\right|_{h=0}\sum_{x}F_x(h)\;=\;\sum_{x}\left.\partial_h^{\,j}\right|_{h=0}F_x(h)'
   r'\qquad\mathrm{(each}\;F_x\;\mathrm{smooth,\;proved\;not\;assumed)}',
 'query_assembly':
   r'\Delta_j(y)\;=\;\sum_{v}M_j(v)\;H_j(y-v)\,\varphi_\sigma(y-v)'
   r'\qquad M_j(v)=\sum_{x:\,f(x)=v}\pi_x\,(-g(x))^{\,j}',
 'query_nonvanish':
   r'T(y)\;=\;c_{v^{*}}H_r(y-v^{*})\;+\;\sum_{v<v^{*}}c_v\,H_r(y-v)\,'
   r'e^{-(v^{*}-v)\,y/\sigma^{2}+\mathrm{const}}',
 'query_hellinger':
   r'\frac{a_E^{2}\,h^{2r}}{32}\;\leq\;H^{2}\;\leq\;\frac{J}{2}\,h^{2r}',
 'query_logsandwich':
   r'H^{2}\;\leq\;-\log\left(1-H^{2}\right)\;\leq\;2H^{2}\qquad (0\leq H^{2}\leq\frac{1}{2})',
 'query_samplecount':
   r'\log\frac{1}{2\varepsilon}\;\leq\;N\,L\qquad\Longrightarrow\qquad \frac{\rho^{N}}{2}\;\leq\;\varepsilon',
 'query_regret':
   r'\frac{\gamma}{4}\,\rho^{2N}\;\leq\;R_N^{*}\;\leq\;\frac{L_{\max}}{2}\,\rho^{N}',
 'query_limit':
   r'\frac{H^{2}}{h^{2r}}\;\longrightarrow\;\frac{1}{8}\int\frac{\Delta_r^{2}}{p_0}\;>\;0',

 # ---------------- STRUCTURAL ----------------
 'struct_family':
   r'g_m=\left(-3,\;(-1)^{p},\;(+1)^{q},\;3\right),\qquad'
   r'p=\left\lceil\frac{m-2}{2}\right\rceil,\;\; q=\left\lfloor\frac{m-2}{2}\right\rfloor,\;\;'
   r'D=\sum_i|g_i|=m+4',
 'struct_dfc':
   r'\mathrm{dfc}(s)\;=\;|s|-|s|\,\mathrm{mod}\,2\qquad\Longrightarrow\qquad'
   r'\mathrm{dfc}(s_k)\;=\;|s_k|-k\,\mathrm{mod}\,2',
 'struct_avg':
   r'\frac{c}{|\mathrm{Bud}|}\;\leq\;\max_{k}\;\mathbb{E}_P\left[r(\pi,k)\right]',
 'struct_path':
   r'c\;\leq\;\mathbb{E}_P\left[\max_{k}\,r(\pi,k)\right]',
 'struct_law':
   r'V_{\mathrm{avg}}=\frac{2}{(m+4)(m-1)},\qquad V_{\mathrm{path}}=\frac{2}{m+4},'
   r'\qquad \frac{V_{\mathrm{path}}}{V_{\mathrm{avg}}}=m-1',
 'struct_marginal':
   r'x^{*}_{i,k}\;=\;\frac{1}{|J|}\#\left\{\,j\;:\;i\in\mathrm{prefix}(\pi_j,k)\,\right\}'
   r'\qquad \sum_i x^{*}_{i,k}=\min(k,n)',
 'struct_cyclic':
   r'\mathrm{cyclic\;menu:}\qquad x^{*}_{i,k}\;=\;\frac{\min(k,m)}{m}\quad\mathrm{for\;every\;item}\;i',

 # ---------------- FUNCTIONAL ----------------
 'func_order':
   r'J_{\mathrm{scalar}}\;\leq\;J_{\mathrm{old}},\qquad J_{\mathrm{full}}\;\leq\;J_{\mathrm{old}},'
   r'\qquad\mathrm{no\;order\;between}\;J_{\mathrm{scalar}}\;\mathrm{and}\;J_{\mathrm{full}}',
 'func_union':
   r'C_j(\lambda)\geq C_i(\lambda)\;\;\Longleftrightarrow\;\;'
   r'\exists\,a,b\;\;\forall\,u,v:\;\;\lambda_{ja}-\lambda_{jb}\;\geq\;\lambda_{iu}-\lambda_{iv}',
 'func_polyhedron':
   r'\mathcal{P}_{ijab}=\left\{\lambda:\;\lambda_{iu}-\lambda_{iv}-\lambda_{ja}+\lambda_{jb}\leq 0'
   r'\;\;\forall u,v\right\}',
 'func_J':
   r'J_\mu(x)\;=\;\min_{i\in T,\;j\notin T,\;a,b}\;\;\inf_{\lambda\in\mathcal{P}_{ijab}}\;'
   r'\frac{1}{2}(\lambda-\mu)^{\top} M(x)\,(\lambda-\mu)',
 'func_oracle':
   r'J(w)=\min_{i\in T,\,j\notin T}\;\inf_{z\geq 0}\left[\,S_i(z)+E_j(z)\,\right]',
 'func_shrink':
   r'S_i(z)=\min_{\ell}\,\frac{1}{2}\sum_{a}\alpha_{ia}\;\mathrm{dist}'
   r'\left(\theta_{ia},\,[\ell,\ell+z]\right)^{2}',
 'func_expand':
   r'E_j(z)=\min_{a\neq b}\;\frac{\left[\,z-(\theta_{ja}-\theta_{jb})\,\right]_+^{2}}'
   r'{2\left(\frac{1}{\alpha_{ja}}+\frac{1}{\alpha_{jb}}\right)}',
 'func_kkt':
   r'M(\lambda^{*}-\mu)+A^{\top}y=0,\qquad y\geq 0,\qquad A\lambda^{*}\leq 0,'
   r'\qquad y^{\top}A\lambda^{*}=0',
 'func_innerqp':
   r'\min\;\frac{1}{2}\sum_{i=1}^{4}w_i\,x_i^{2}\;\;\mathrm{s.t.}\;\;x_1-x_2-x_3+x_4\geq g'
   r'\qquad=\qquad\frac{g^{2}}{2\left(\frac{1}{w_1}+\frac{1}{w_2}+\frac{1}{w_3}+\frac{1}{w_4}\right)}',
 'func_family1':
   r'0\;\leq\;\frac{J_{\mathrm{full}}}{J_{\mathrm{scalar}}}\;\leq\;9\eta\;\longrightarrow\;0'
   r'\qquad (J_{\mathrm{scalar}}=\frac{1}{32})',
 'func_family2':
   r'\frac{J_{\mathrm{full}}}{J_{\mathrm{scalar}}}\;\geq\;\frac{1+3\eta}{16\eta}\;'
   r'\longrightarrow\;+\infty\qquad (J_{\mathrm{full}}\geq\frac{1}{128})',
 'func_breakeven':
   r'\min_{p}\left[\frac{\sigma_a^{2}}{p}+\frac{\sigma_b^{2}}{1-p}\right]=(\sigma_a+\sigma_b)^{2}'
   r'\qquad\Longrightarrow\qquad \mathrm{break\,even\;at}\;\; c_c\,\nu_c=(\sigma_a+\sigma_b)^{2}',
 'func_crossing':
   r'B_{*}\;=\;\kappa\,\frac{|S_2|\,\Gamma_2-|S_1|\,\Gamma_1}{\Gamma_2-\Gamma_1}',
}


def render(key, tex, fontsize=30, color=INK, dpi=300):
    fig = plt.figure(figsize=(0.02, 0.02))
    fig.text(0, 0, f'${tex}$', fontsize=fontsize, color=color)
    p = OUT / f'{key}.png'
    fig.savefig(p, dpi=dpi, bbox_inches='tight', pad_inches=0.06, transparent=True)
    plt.close(fig)
    from PIL import Image
    w, h = Image.open(p).size
    return p, w, h


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefix', default='')
    ap.add_argument('--index', default='research/papers/_figures/eq/index.json')
    a = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    idx = {}
    bad = []
    for k, tex in EQUATIONS.items():
        if a.prefix and not k.startswith(a.prefix):
            continue
        col = CRAN if k in ('master_rate', 'query_regret', 'struct_law', 'func_J') else INK
        size = 38 if k in ('master_rate', 'query_regret', 'struct_law', 'func_J') else 30
        try:
            p, w, h = render(k, tex, fontsize=size, color=col)
        except Exception as e:
            msg = str(e).strip().splitlines()[-1]
            bad.append((k, msg))
            print(f'  {k:26} FAILED  {msg[:80]}')
            continue
        idx[k] = {'path': str(p), 'px_w': w, 'px_h': h, 'aspect': round(w / h, 4)}
        print(f'  {k:26} {w:5d}x{h:<5d} aspect {w/h:6.2f}')
    Path(a.index).write_text(json.dumps(idx, indent=1))
    print(f'index: {a.index}   rendered {len(idx)}, failed {len(bad)}')
    if bad:
        print('FAILURES (mathtext does not accept these):')
        for k, m in bad:
            print(f'  {k}: {m}')


if __name__ == '__main__':
    main()
