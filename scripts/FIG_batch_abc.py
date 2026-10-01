#!/usr/bin/env python3
"""Figures for the artifacts produced after the last corrections round.

Evidence classes are printed on every panel and mean what they say:

    EXACT        rational arithmetic or a verified certificate
    NUMERICAL    a solved value or a measured quantity, floating point
    ILLUSTRATION a formula plotted, carrying no new evidence

No panel here plots a formula as if it were data.  Where a proved bound is drawn alongside
measurements, it is drawn as a line and named as a bound, and where that bound is vacuous
the panel says so rather than letting the eye supply agreement.
"""

import json
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

IN = "research/unified_20260919"
OUT = "research/papers/_figures"
plt.rcParams.update({"font.size": 7, "axes.linewidth": 0.6,
                     "xtick.major.width": 0.6, "ytick.major.width": 0.6})


def load(name):
    with open(f"{IN}/{name}") as f:
        return json.load(f)


def tag(ax, text):
    ax.text(0.02, 0.98, text, transform=ax.transAxes, va="top", ha="left",
            fontsize=5.5, color="#444", bbox=dict(boxstyle="round,pad=0.2",
                                                  fc="white", ec="#bbb", lw=0.4))


def fig_separation():
    """A-separation: the two solved ratios against the two proved bounds."""
    d = load("paperA_separation_games.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    lo, hi = d["family_low"], d["family_high"]

    M = [r["M"] for r in lo]
    ax[0].loglog(M, [r["ratio"] for r in lo], "o-", ms=4, color="#4C72B0",
                 label="solved ratio")
    ax[0].loglog(M, [r["bound_64_over_M"] for r in lo], "--", color="#C44E52",
                 label=r"proved bound $64/M$")
    ax[0].set_xlabel("$M$")
    ax[0].set_ylabel(r"$\Gamma_{\rm true}/\Gamma_{\rm proxy}$")
    ax[0].set_title("A-low: the proxy overprices")
    ax[0].legend(frameon=False, fontsize=6)
    tag(ax[0], "NUMERICAL (cutting-plane, duality gap closed)")

    M2 = [r["M"] for r in hi]
    ax[1].loglog(M2, [r["ratio"] for r in hi], "s-", ms=4, color="#4C72B0",
                 label="solved ratio")
    ax[1].loglog(M2, [r["bound_M_over_96"] for r in hi], "--", color="#55A868",
                 label=r"proved bound $M/96$")
    ax[1].set_xlabel("$M$")
    ax[1].set_title("A-high: the proxy underprices")
    ax[1].legend(frameon=False, fontsize=6)
    tag(ax[1], "NUMERICAL, certificates in the JSON")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperA_separation_games.pdf")
    plt.close(fig)
    return "paperA_separation_games.pdf"


def fig_repair():
    """A-repair: the barrier certificate against the oracle error it controls."""
    d = load("paperA_repair_barrier.json")
    pts = [p for r in d["rows"] for p in r["points"]]
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))

    fired = [p for p in pts if p["fired"]]
    unf = [p for p in pts if not p["fired"]]
    for grp, col, lab, mk in ((unf, "#C44E52", "barrier does not fire", "."),
                              (fired, "#55A868", "barrier fires", "o")):
        x = [max(p["ratio_proxy_over_barrier"], 1e-6) for p in grp]
        y = [max(p["rel_err"], 1e-16) for p in grp]
        ax[0].loglog(x, y, mk, ms=3, color=col, label=lab, alpha=0.7)
    ax[0].axvline(1.0, color="k", ls="--", lw=0.8)
    ax[0].set_xlabel(r"$J_{\rm proxy}(w)/B_{\rm switch}(w)$")
    ax[0].set_ylabel("relative oracle error")
    ax[0].set_title("the certificate and the error it controls")
    ax[0].legend(frameon=False, fontsize=6)
    tag(ax[0], "NUMERICAL; soundness is the theorem")

    fr = d["best_among_sampled_designs"]
    lowr = [r for r in fr if r["proved_ceiling"] is not None]
    Ms = [r["M"] for r in lowr]
    ax[1].semilogx(Ms, [r["best_among_sampled_designs"] for r in lowr], "o-", ms=4,
                   color="#4C72B0", label="best among SAMPLED designs")
    ceil = [min(r["proved_ceiling"], 1.05) for r in lowr]
    ax[1].semilogx(Ms, ceil, "--", color="#C44E52",
                   label=r"proved ceiling $\min(64/M,1)$")
    vac = [r["M"] for r in lowr if r["proved_ceiling"] >= 1.0]
    if vac:
        ax[1].axvspan(min(vac) * 0.7, max(vac) * 1.4, color="#999", alpha=0.12)
        ax[1].text(np.sqrt(min(vac) * max(vac)), 0.8, "ceiling vacuous here",
                   fontsize=5.5, ha="center", color="#555")
    ax[1].set_ylim(-0.03, 1.1)
    ax[1].set_xlabel("$M$")
    ax[1].set_ylabel("fraction of the proxy game")
    ax[1].set_title("what certification can reach")
    ax[1].legend(frameon=False, fontsize=6, loc="upper right")
    tag(ax[1], "sampled = NUMERICAL lower bound; ceiling = EXACT")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperA_repair_barrier.pdf")
    plt.close(fig)
    return "paperA_repair_barrier.pdf"


def fig_b_uniform_hellinger():
    """Paper B: the per-step Hellinger bound, and what the degree cap buys."""
    d = load("paperB_uniform_hellinger.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    cols = {"2": "#4C72B0", "3": "#C44E52"}
    for rk, rec in sorted(d["results"].items()):
        r = int(rk)
        hs = np.array(rec["h"])
        sv = np.array([x["sup"] for x in rec["v"]])
        su = np.array([x["sup"] for x in rec["u"]])
        ax[0].loglog(hs, sv, "o-", ms=4, color=cols.get(rk, "k"),
                     label=fr"$r={r}$ identify (order {rec['order_v']:.1f})")
        ax[0].loglog(hs, su, "s--", ms=4, color=cols.get(rk, "k"), alpha=0.55,
                     label=fr"$r={r}$ decide (order {rec['order_u']:.1f})")
    ax[0].set_xlabel(r"$h$")
    ax[0].set_ylabel(r"$\sup_g H^2$")
    ax[0].set_title("per-step separation, over the query class")
    ax[0].legend(frameon=False, fontsize=5.5)
    tag(ax[0], "NUMERICAL; (B4) and the reduction to it are both PROVED")

    for rk, rec in sorted(d["results"].items()):
        hs = np.array(rec["h"])
        sv = np.array([x["sup"] for x in rec["v"]])
        vf = np.array([x["sup"] for x in rec["vfull"]])
        ax[1].loglog(hs, sv, "o-", ms=4, color=cols.get(rk, "k"),
                     label=fr"$r={rk}$, degree $\leq r-1$")
        ax[1].loglog(hs, vf, "x:", ms=5, color=cols.get(rk, "k"), alpha=0.7,
                     label=fr"$r={rk}$, no degree cap")
    ax[1].set_xlabel(r"$h$")
    ax[1].set_ylabel(r"$\sup_g H^2$ (identify)")
    ax[1].set_title("the degree cap is what creates the separation")
    ax[1].legend(frameon=False, fontsize=5.5)
    tag(ax[1], "remove the cap and identification costs no more than deciding")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperB_uniform_hellinger.pdf")
    plt.close(fig)
    return "paperB_uniform_hellinger.pdf"


def fig_c_general_m():
    """Paper C: the breakpoint law across sizes, with what is proved on each side."""
    d = load("paperC_general_m.json")
    from fractions import Fraction as Fr
    ms = sorted(int(k) for k in d["sizes"])
    eta = [float(Fr(d["sizes"][str(m)]["eta_law"])) for m in ms]
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    odd = [(m, e) for m, e in zip(ms, eta) if m % 2]
    even = [(m, e) for m, e in zip(ms, eta) if m % 2 == 0]
    ax[0].plot([m for m, _ in odd], [e for _, e in odd], "o", ms=4,
               color="#C44E52", label=r"$m$ odd: $\eta_*=1$")
    ax[0].plot([m for m, _ in even], [e for _, e in even], "s", ms=4,
               color="#4C72B0", label=r"$m$ even: $\eta_*=\frac{m-2}{2(m-1)}$")
    ax[0].axhline(0.5, color="k", ls=":", lw=0.8)
    ax[0].text(ms[-1], 0.52, r"$1/2$", ha="right", fontsize=6)
    ax[0].set_xlabel(r"$m$")
    ax[0].set_ylabel(r"$\eta_*(m)$")
    ax[0].set_ylim(0, 1.15)
    ax[0].set_title("the breakpoint, by parity")
    ax[0].legend(frameon=False, fontsize=6, loc="center right")
    cross = d.get("cross_check", {})
    tag(ax[0], f"CONSTRUCTIVE upper side at every $m$; {len(cross)} sizes also"
               " carry a Farkas certificate")

    # what the construction's band slack does around the law's eta
    ax[1].axhline(0.0, color="k", lw=0.8)
    at = [float(Fr(d["sizes"][str(m)]["band_slack_at_eta"])) for m in ms]
    be = [float(Fr(d["sizes"][str(m)]["band_slack_just_below"])) for m in ms]
    ax[1].plot(ms, at, "o-", ms=3, color="#4C72B0",
               label=r"slack at $\eta_*(m)$")
    ax[1].plot(ms, be, "x-", ms=4, color="#C44E52",
               label=r"slack at $\eta_*(m)-10^{-6}$")
    ax[1].set_xlabel(r"$m$")
    ax[1].set_ylabel("worst marginal-band slack")
    ax[1].set_title("the construction is tight at the law")
    ax[1].legend(frameon=False, fontsize=6)
    tag(ax[1], "EXACT rational arithmetic; slack is $0$ at $\\eta_*$ and $<0$ below it")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperC_general_m.pdf")
    plt.close(fig)
    return "paperC_general_m.pdf"


def fig_a7():
    """A7: the panel per alpha, and the alpha axis read as a SLOPE.

    An earlier version of this figure plotted `tau/log(1/alpha)` against a band for
    `1/Gamma_comp`.  That is a comparison of LEVELS, and the levels are not testable on this
    panel: the stopping threshold carries `(1/2) sum_e log(1 + N_e/a)`, measured at ~19.7
    against `log(1/alpha) <= 4.61`, so the ratio is dominated by the penalty and not by the
    rate.  Drawing the benchmark band beside it invited exactly the reading the analysis
    rules out.  An additive penalty cancels in the SLOPE, so that is what the right panel
    shows, with the prediction corrected for the penalty's own measured drift.
    """
    d = load("paperA7_learner.json")
    scope = d.get("panel_scope")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    alphas = [r["alpha"] for r in d["rows"]]
    L = np.log(1.0 / np.array(alphas))

    # ---- left: the panel itself, per alpha, with standard errors ----------------
    for arm, col, mk in (("learner", "#4C72B0", "o"),
                         ("oracle", "#55A868", "s"),
                         ("uniform", "#C44E52", "^")):
        mus = np.array([r["arms"][arm]["mean_tau"] for r in d["rows"]])
        cens = sum(r["arms"][arm]["censored"] for r in d["rows"])
        if scope:
            sems = np.array([c["arms"][arm]["sem"] for c in scope["per_alpha"]])
        else:
            sems = np.zeros_like(mus)
        lab = arm + (" (diagnostic, NOT a lower bound)" if arm == "oracle" else "")
        lab += f"  [{cens} censored]" if cens else ""
        ax[0].errorbar(L, mus, yerr=sems, fmt=mk + "-", ms=4, capsize=2,
                       color=col, label=lab)
    ax[0].set_xlabel(r"$\log(1/\alpha)$")
    ax[0].set_ylabel(r"mean $\tau$")
    ax[0].set_title("stopping time per confidence level")
    ax[0].legend(frameon=False, fontsize=5.5)
    tag(ax[0], "NUMERICAL; common random numbers across $\\alpha$; bars are $\\pm$1 s.e.")

    # ---- right: the slope, which is the part that IS testable -------------------
    try:
        sl = load("paperA7_alpha_slope.json")
    except FileNotFoundError:
        sl = None
    if sl is not None:
        arms = ("learner", "oracle", "uniform")
        cols = ("#4C72B0", "#55A868", "#C44E52")
        xs = np.arange(len(arms))
        vals = [sl["per_arm"][a]["slope_mean"] for a in arms]
        errs = [1.96 * sl["per_arm"][a]["slope_sem"] for a in arms]
        ax[1].errorbar(xs, vals, yerr=errs, fmt="o", ms=5, capsize=3,
                       color="k", ecolor="0.4", lw=0)
        for x, v, c in zip(xs, vals, cols):
            ax[1].plot([x], [v], "o", ms=5, color=c)
        pred = sl.get("predicted_slope_with_drift")
        if pred:
            ax[1].axhspan(pred[0], pred[1], color="#f0c674", alpha=0.55, zorder=0,
                          label="predicted $1/\\Gamma$, penalty drift included")
            ax[1].axhline(pred[0], color="#a07a10", lw=0.8)
        inv = sl.get("inv_Gamma_comp_bracket")
        if inv:
            ax[1].axhline(inv[0], color="k", ls=":", lw=0.8,
                          label=r"$1/\Gamma_{\rm comp}$ (no drift)")
        ax[1].set_xticks(xs)
        ax[1].set_xticklabels(arms)
        ax[1].set_ylabel(r"$d\bar\tau\,/\,d\log(1/\alpha)$")
        ax[1].set_title("slope in $\\log(1/\\alpha)$ (the testable part)")
        ax[1].legend(frameon=False, fontsize=5.5, loc="upper left")
        tag(ax[1], "NUMERICAL; bars are 95% CI over paths. LEVELS are NOT\ncomparable"
                   " with $1/\\Gamma$: threshold penalty $\\approx$ 19.7 vs $\\log(1/\\alpha)\\leq$ 4.6")
    else:
        corr, tot = [], []
        for r in d["rows"]:
            c = sum(r["arms"][a]["correct"] for a in ("learner", "oracle", "uniform"))
            n = sum(r["arms"][a]["n_runs"] - r["arms"][a]["censored"]
                    for a in ("learner", "oracle", "uniform"))
            corr.append(c); tot.append(n)
        ax[1].bar(range(len(alphas)), [c / max(t, 1) for c, t in zip(corr, tot)],
                  color="#4C72B0", width=0.6)
        ax[1].set_xticks(range(len(alphas)))
        ax[1].set_xticklabels([f"{a:g}" for a in alphas])
        ax[1].set_ylim(0, 1.15)
        ax[1].set_xlabel(r"$\alpha$")
        ax[1].set_ylabel("fraction correct")
        tag(ax[1], "NUMERICAL")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperA7_learner.pdf")
    plt.close(fig)
    return "paperA7_learner.pdf"


def fig_b_collapse():
    """B: the two moment tests, each against its own scaling variable."""
    d = load("paperB_moment_tests.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    cols = ["#4C72B0", "#55A868", "#C44E52", "#8172B2", "#CCB974"]
    for k, (r, res) in enumerate(sorted(d["results"].items())):
        for j, panel in enumerate(("decision", "ident")):
            hs = sorted({p["h"] for p in res[panel]})
            for i, h in enumerate(hs):
                pts = sorted([p for p in res[panel] if p["h"] == h],
                             key=lambda p: p["scaled"])
                ax[j].semilogx([p["scaled"] for p in pts], [p["err"] for p in pts],
                               "o-", ms=3, lw=0.8, color=cols[i % len(cols)],
                               alpha=0.85,
                               label=(f"$h={h:g}$" if k == 0 else None))
    ax[0].set_xlabel(r"$N h^2$"); ax[0].set_ylabel("error rate")
    ax[0].set_title("decision: collapse on $Nh^2$")
    ax[0].legend(frameon=False, fontsize=5.5, ncol=2)
    tag(ax[0], "NUMERICAL: tests were RUN, no formula plotted")
    ax[1].set_xlabel(r"$N h^{2r}$")
    ax[1].set_title("identification: collapse on $Nh^{2r}$")
    tag(ax[1], "NUMERICAL; curves per $h$, not a fitted law")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperB_moment_tests.pdf")
    plt.close(fig)
    return "paperB_moment_tests.pdf"


def fig_c_certificates():
    """C: the breakpoint from the direct LP, with the exact Farkas root."""
    lp = load("paperC_breakpoint_lp.json")["rows"]
    du = load("paperC_exact_dual.json")["rows"]
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))

    ms = [r["m"] for r in lp if r.get("ok")]
    eta = [r["eta_lp"] for r in lp if r.get("ok")]
    conj = [float(eval(r["conjecture"])) for r in lp if r.get("ok")]
    ax[0].plot(ms, conj, "-", color="#C44E52", lw=1.0, label="parity formula")
    ax[0].plot(ms, eta, "o", ms=5, color="#4C72B0", label="direct LP (no bisection)")
    ax[0].set_xlabel("$m$"); ax[0].set_ylabel(r"$\eta_*$")
    ax[0].set_title("breakpoint, solved in one LP")
    ax[0].legend(frameon=False, fontsize=6)
    tag(ax[0], "NUMERICAL LP; primal flows exported as exact rationals")

    dm = [r["m"] for r in du if r.get("root_matches_conjecture")]
    ax[1].plot(dm, [1.0] * len(dm), "*", ms=11, color="#55A868",
               label="Farkas root $=\\eta_*$ exactly")
    other = [r["m"] for r in du if not r.get("root_matches_conjecture")]
    if other:
        ax[1].plot(other, [0.0] * len(other), "x", ms=6, color="#C44E52",
                   label="no matching root")
    ax[1].set_ylim(-0.2, 1.3)
    ax[1].set_yticks([0, 1])
    ax[1].set_yticklabels(["open", "closed"])
    ax[1].set_xlabel("$m$")
    ax[1].set_title("obligation (O2), per size")
    ax[1].legend(frameon=False, fontsize=6, loc="center right")
    tag(ax[1], "EXACT: multipliers verified in Fractions")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperC_certificates.pdf")
    plt.close(fig)
    return "paperC_certificates.pdf"


def fig_b_envelope():
    """Paper B: the proved envelope chain -- the rate, and the bound that carries it."""
    d = load("paperB_envelope_rate.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    cols = {"2": "#4C72B0", "3": "#C44E52", "4": "#55A868"}

    for rk, rec in sorted(d["rate"].items()):
        hs = np.array([x["h"] for x in rec["rows"]])
        it = np.array([x["integral"] for x in rec["rows"]])
        hb = np.array([x["head_bound"] for x in rec["rows"]])
        ax[0].loglog(hs, it, "o-", ms=4, color=cols.get(rk, "k"),
                     label=fr"$r={rk}$: $\int\Delta^2/\ell$ (order {rec['order']:.2f})")
        ax[0].loglog(hs, hb, "--", lw=0.9, color=cols.get(rk, "k"), alpha=0.7,
                     label=fr"$r={rk}$: proved $h^{{2r}}r^{{-2r}}C$")
    ax[0].set_xlabel(r"$h$")
    ax[0].set_ylabel(r"$\int \Delta^2/\ell$")
    ax[0].set_title("the rate, against the proved bound")
    ax[0].legend(frameon=False, fontsize=5.0, ncol=1)
    tag(ax[0], "PROVED upper bound; the gap is the explicit constant, not sharpness")

    y = np.array(d["curve"]["y"])
    for rk in sorted(d["rate"]):
        ax[1].semilogy(y, np.array(d["curve"][f"ratio_r{rk}"]), "-", lw=1.0,
                       color=cols.get(rk, "k"), label=fr"$r={rk}$: envUp$^2$/envLo")
        ax[1].semilogy(y, np.array(d["curve"][f"dom_r{rk}"]), ":", lw=0.9,
                       color=cols.get(rk, "k"), alpha=0.7)
    ax[1].set_xlabel(r"$y$")
    ax[1].set_ylabel("envelope ratio")
    ax[1].set_ylim(1e-20, None)
    ax[1].set_title(r"dominated by $C\,e^{-y^2/4\sigma^2}$ (dotted)")
    ax[1].legend(frameon=False, fontsize=5.5)
    tag(ax[1], "EXACT: every point satisfies the proved inequality")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperB_envelope_rate.pdf")
    plt.close(fig)
    return "paperB_envelope_rate.pdf"


def fig_a7_chain():
    """Paper A7: why a fixed mesh fails, and the t^{-3/2} window tail."""
    d = load("paperA7_stopping_chain.json")
    c = d["curve"]
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))

    u = np.array(c["u"])
    ax[0].plot(u, np.array(c["rate"]), "-", lw=1.1, color="#4C72B0",
               label=r"$u\Delta-u^2/2$")
    ax[0].axhline(0.0, color="#888", lw=0.6)
    ax[0].axhline(c["info"], color="#C44E52", ls="--", lw=0.9,
                  label=fr"information $\Delta^2/2={c['info']:.4f}$")
    fg = np.array(c["fixed_grid"]); fr = np.array(c["fixed_rate"])
    keep = (fg >= u.min()) & (fg <= u.max())
    ax[0].plot(fg[keep], fr[keep], "s", ms=5, color="#C44E52",
               label=fr"fixed mesh $d={c['fixed_grid'][1]-c['fixed_grid'][0]:.2f}$"
                     " (all $<0$)")
    ax[0].plot([c["mesh_point"]], [c["mesh_rate"]], "o", ms=6, color="#55A868",
               label=fr"mesh $m={c['mesh']}$: rate $\geq\Delta^2/2-m^2/2$")
    ax[0].set_xlabel(r"tilt $u$")
    ax[0].set_ylabel("growth rate")
    ax[0].set_title("a fixed mesh is the whole obstruction")
    ax[0].legend(frameon=False, fontsize=5.0, loc="lower center")
    tag(ax[0], r"EXACT: the loss is the squared miss, $(u-\Delta)^2/2$")

    t = np.array([r["t"] for r in d["window"]])
    wb = np.array([r["window_bound"] for r in d["window"]])
    tp = np.array([r["t_pow"] for r in d["window"]])
    ax[1].loglog(t, wb, "o-", ms=4, color="#4C72B0",
                 label=r"$1/(\lceil\sqrt{t}\rceil-1)^3$")
    ax[1].loglog(t, tp, "--", lw=0.9, color="#C44E52", label=r"proved $8\,t^{-3/2}$")
    ax[1].set_xlabel(r"$t$")
    ax[1].set_ylabel(r"$\Pr(\tau>t)$ bound")
    ax[1].set_title(r"the $\sqrt{t}$ window gives a summable tail")
    ax[1].legend(frameon=False, fontsize=5.5)
    tag(ax[1], "EXACT; the per-step confidence input is NOT simulated")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperA7_stopping_chain.pdf")
    plt.close(fig)
    return "paperA7_stopping_chain.pdf"


def fig_b_crossover():
    """Paper B: how little nonlinearity destroys the decision/identification gap."""
    d = load("paperB_crossover.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))

    ob = d["order_by_eta"]
    ax[0].plot([x["eta"] for x in ob], [x["order"] for x in ob], "o-", ms=4,
               color="#4C72B0")
    ax[0].axhline(6.0, ls="--", lw=0.9, color="#55A868", label=r"cube channel, order $6$")
    ax[0].axhline(4.0, ls="--", lw=0.9, color="#C44E52", label=r"square channel, order $4$")
    ax[0].set_xlabel(r"$\eta$")
    ax[0].set_ylabel(r"measured order of $H^2$ in $h$")
    ax[0].set_title("the order falls from six to four")
    ax[0].legend(frameon=False, fontsize=5.5)
    tag(ax[0], "NUMERICAL; the moment algebra behind it is EXACT")

    cols = ["#4C72B0", "#C44E52", "#55A868", "#8172B2", "#CCB974", "#64B5CD", "#937860"]
    etas = sorted({r["eta"] for r in d["rows"]})
    c6, c4 = d["fit"]["c6"], d["fit"]["c4"]
    for k, e in enumerate(etas):
        sub = sorted([r for r in d["rows"] if r["eta"] == e], key=lambda r: r["h"])
        hh = np.array([r["h"] for r in sub]); vv = np.array([r["H2"] for r in sub])
        ax[1].loglog(hh, vv, "o-", ms=3, lw=0.9, color=cols[k % len(cols)],
                     label=fr"$\eta={e}$")
        if e <= d["fit"].get("eta_fit_max", 0.4):
            ax[1].loglog(hh, c6 * hh ** 6 + c4 * e ** 2 * hh ** 4, ":", lw=0.9,
                         color=cols[k % len(cols)], alpha=0.8)
    ax[1].set_xlabel(r"$h$")
    ax[1].set_ylabel(r"$H^2$")
    ax[1].set_title(r"two additive channels (dotted: fitted form)")
    ax[1].legend(frameon=False, fontsize=5.0, ncol=2)
    tag(ax[1], "fit on the coarse half, drawn through the fine half")

    fig.tight_layout()
    fig.savefig(f"{OUT}/paperB_crossover.pdf")
    plt.close(fig)
    return "paperB_crossover.pdf"


def main():
    made = []
    for f in (fig_separation, fig_repair, fig_a7, fig_b_collapse, fig_c_certificates,
              fig_c_general_m, fig_b_uniform_hellinger, fig_b_envelope,
              fig_a7_chain, fig_b_crossover):
        try:
            made.append(f())
            print(f"  wrote {made[-1]}")
        except FileNotFoundError as e:
            print(f"  SKIPPED {f.__name__}: missing artifact {e.filename}",
                  file=sys.stderr)
        except Exception as e:
            print(f"  FAILED {f.__name__}: {type(e).__name__}: {e}", file=sys.stderr)
    print(f"\n{len(made)} figures written")
    return 0 if made else 1


if __name__ == "__main__":
    sys.exit(main())
