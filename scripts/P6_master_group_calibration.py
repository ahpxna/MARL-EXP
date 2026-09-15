#!/usr/bin/env python3
"""MASTER batch-2 package: when must a GROUP of calibration queries be bought,
although every single one of them is useless on its own?

THE MODEL.  Y_e = m_theta(e) + v_e^T b + Z_e with a VECTOR nuisance b in R^p (not
the common-offset scalar of the earlier chain -- the change is explicit, and the
scalar case is kept as the negative control below).  With d_{u,e} = m_theta(e) -
m_{lambda_u}(e), a_e = x_e/nu_e,
    D_u = (1/2) sum_e a_e d_{u,e}^2,   M_u = sum_e a_e d_{u,e} v_e,
    K   = sum_e a_e v_e v_e^T,         I_u = D_u - (1/2) M_u^T K^{-1} M_u,
the last being the profile over the nuisance, i.e. I_u(x) = min_t sum_e
(x_e/nu_e)(d_{u,e} - v_e^T t)^2/2.

THE DERIVATIVE, WITH THE OPPORTUNITY COST.  Keep the ordinary allocation
proportions fixed, move a fraction t of the budget to controls with mixture rho.
Then K(t) = (1-t)K + t C with C = sum_l (rho_l/(kappa_l nu_l)) c_l c_l^T, while D_u
and M_u only scale by (1-t).  Differentiating I_u(t) at t = 0 gives
    dI_u/dt|_0 = sum_l rho_l G_{u,l} - I_u,   G_{u,l} = (c_l^T K^{-1} M_u)^2/(2 nu_l kappa_l),
so on the active set A_0 = {u : I_u = V_0} the directional derivative of the value is
    Lambda - V_0,   Lambda = max_rho min_{u in A_0} sum_l rho_l G_{u,l}.
The -V_0 is the budget taken away from ordinary queries and is NOT dropped.  The
derivative formula is checked here against a finite-difference of the exact
profiled value.

THE NEGATIVE CONTROL, WHICH IS A THEOREM.  If p = 1 then K, M_u, c_l are scalars
and G_{u,l} = alpha_u beta_l factorises, so
    min_u sum_l rho_l alpha_u beta_l = (sum_l rho_l beta_l) min_u alpha_u
                                     <= (max_l beta_l) min_u alpha_u
                                     =  max_l min_u G_{u,l},
i.e. a MIXTURE of controls can never beat the best SINGLE control.  Complementarity
therefore requires rank >= 2 in the nuisance.  This is the statement formalised in
`LeanMasterGroupCalibrationV1.lean`; here it is checked numerically as well.

THE CONSTRUCTION, BUILT FROM QUERY MEANS -- NOT TYPED IN AS A MATRIX.
Four items, two instruments, p = 2 offsets:
    queries  (item1, instr1), (item2, instr1), (item3, instr2), (item4, instr2),
    m_theta(e) = theta_item,  v_e = e_instr,  nu_e = 1,  theta = (1, 0, 0, 1),
    answer = the items strictly above 1/2, i.e. {1, 4};
    the four boundary alternatives move ONE item onto 1/2, so
    d_{u1} = (1/2,0,0,0), d_{u2} = (0,-1/2,0,0), d_{u3} = (0,0,-1/2,0),
    d_{u4} = (0,0,0,1/2).
Controls c_1 = e_1, c_2 = e_2 read one offset each.  Because items 1,2 are seen
only through instrument 1 and items 3,4 only through instrument 2, control 1 is
blind to u3,u4 and control 2 is blind to u1,u2: G is BLOCK diagonal.  Every single
control therefore leaves an active alternative with zero gain, so its directional
derivative is exactly -V_0 < 0 -- buying it alone strictly HURTS -- while the even
mixture gives Lambda = (3/2) V_0 > V_0.  Every number is recomputed from the model.

THE FULL-CLASS OPTIMUM.  The primal max_x min_u I_u over ordinary queries AND
controls is solved as the concave programme it is (I_u is a min of linear functions
of x, and dI_u/dx_e = (d_{u,e} - v_e^T t_u)^2/(2 nu_e) with t_u = K^{-1}M_u), and
the dual
    H_e = sum_u lambda_u (d_{u,e} - v_e^T t_u)^2/(2 nu_e),
    H_l^ctrl = sum_u lambda_u (c_l^T t_u)^2/(2 nu_l)
is checked against H/cost <= V for EVERY ordinary query and EVERY control.

WHAT THIS DOES NOT ESTABLISH.
  * The active set A_0 is read at a numerical tolerance; the threshold theorem is
    verified on this instance, not proved for all instances.
  * The full-class optimum has a closed form here (V = 3(3-2 sqrt2)/32) and its
    dual is tight on every ordinary query and every control, but the check runs in
    floating point, not in exact arithmetic.
  * Nothing here says the vector-nuisance model is the right model for MASTER; it
    is an explicit extension, and the p = 1 negative control says the earlier
    common-offset model CANNOT show this effect.

    .venv/bin/python scripts/P6_master_group_calibration.py
"""
from __future__ import annotations

import itertools, json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

REPO = Path(__file__).resolve().parents[1]


class Instance:
    def __init__(self, d, V, nu, cost, ctrl_c, ctrl_nu, ctrl_kappa):
        self.d = np.array(d, float)          # (n_alt, n_query)
        self.V = np.array(V, float)          # (n_query, p)
        self.nu = np.array(nu, float)
        self.cost = np.array(cost, float)
        self.C = np.array(ctrl_c, float)     # (n_ctrl, p)
        self.cnu = np.array(ctrl_nu, float)
        self.ckap = np.array(ctrl_kappa, float)
        self.p = self.V.shape[1]

    def KMD(self, x):
        a = x / self.nu
        K = (self.V * a[:, None]).T @ self.V
        M = (self.d * a[None, :]) @ self.V           # (n_alt, p)
        D = 0.5 * (self.d ** 2 * a[None, :]).sum(1)
        return K, M, D

    def info(self, x):
        K, M, D = self.KMD(x)
        Ki = np.linalg.pinv(K)
        return D - 0.5 * np.einsum('up,pq,uq->u', M, Ki, M), K, M, Ki

    def G(self, x):
        I, K, M, Ki = self.info(x)
        T = M @ Ki                                    # t_u = K^{-1} M_u
        num = (self.C @ T.T) ** 2                     # (n_ctrl, n_alt)
        return (num / (2 * self.cnu * self.ckap)[:, None]).T, I, T


def build_instance(theta=(1.0, 0.0, 0.0, 1.0), thr=0.5, ctrl_kappa=(2 / 3, 2 / 3)):
    """the four-item / two-instrument model described in the docstring."""
    theta = np.array(theta, float)
    instr = [0, 0, 1, 1]                       # item i is read by instrument instr[i]
    n = len(theta)
    V = np.zeros((n, 2))
    for i, g in enumerate(instr):
        V[i, g] = 1.0
    d = []
    labels = []
    for i in range(n):
        lam = theta.copy(); lam[i] = thr       # move item i onto the boundary
        d.append(theta - lam)
        labels.append(f"item{i+1} crosses the threshold")
    return Instance(d, V, np.ones(n), np.ones(n),
                    np.eye(2), np.ones(2), ctrl_kappa), labels, instr


def optimise_ordinary(inst, starts=12):
    """max over ordinary allocations of min_u I_u, with the analytic gradient."""
    n = len(inst.cost)

    def negval(z):
        x = np.maximum(z, 1e-12); x = x / float(inst.cost @ x)
        I, _, _, _ = inst.info(x)
        return -float(np.min(I))
    rng = np.random.default_rng(20260914)
    best = (None, -np.inf)
    for s in range(starts):
        x0 = np.ones(n) if s == 0 else np.abs(rng.standard_normal(n)) + 0.1
        x0 = x0 / float(inst.cost @ x0)
        r = minimize(negval, x0, method="Nelder-Mead",
                     options={"maxiter": 20000, "xatol": 1e-12, "fatol": 1e-14})
        x = np.maximum(r.x, 0); x = x / float(inst.cost @ x)
        v = -negval(x)
        if v > best[1]:
            best = (x, v)
    return best


def full_class_optimum(inst, starts=16):
    """max over ordinary queries AND controls of min_u I_u, as the CONCAVE
    programme it is.  I_u(z) = min_t sum_e (z_e/nu_e)(d_{u,e} - v_e^T t)^2/2 is a
    minimum of linear functions of z, hence concave, and the envelope theorem gives
        dI_u/dz_e = (d_{u,e} - v_e^T t_u)^2 / (2 nu_e),   t_u = K^{-1} M_u,
    with d = 0 for a control.  Nelder-Mead on this returns asymmetric, unconverged
    points; SLSQP with those gradients does not."""
    n, L = len(inst.cost), len(inst.ckap)
    cost = np.concatenate([inst.cost, inst.ckap])
    nuall = np.concatenate([inst.nu, inst.cnu])
    Vall = np.vstack([inst.V, inst.C])
    dall = np.hstack([inst.d, np.zeros((inst.d.shape[0], L))])
    nu_alt = inst.d.shape[0]

    def info(z):
        a = z / nuall
        K = (Vall * a[:, None]).T @ Vall
        M = (dall * a[None, :]) @ Vall
        D = 0.5 * (dall ** 2 * a[None, :]).sum(1)
        Ki = np.linalg.pinv(K)
        T = M @ Ki
        I = D - 0.5 * np.einsum('up,pq,uq->u', M, Ki, M)
        Gr = (dall - T @ Vall.T) ** 2 / (2 * nuall)[None, :]
        return I, Gr, T, K

    def cons_f(w):
        I, _, _, _ = info(np.maximum(w[:-1], 1e-12))
        return I - w[-1]

    def cons_j(w):
        _, Gr, _, _ = info(np.maximum(w[:-1], 1e-12))
        J = np.zeros((nu_alt, len(w)))
        J[:, :-1] = Gr
        J[:, -1] = -1.0
        return J

    cons = [{"type": "ineq", "fun": cons_f, "jac": cons_j},
            {"type": "ineq", "fun": lambda w: 1.0 - float(cost @ w[:-1]),
             "jac": lambda w: np.concatenate([-cost, [0.0]])}]
    rng = np.random.default_rng(7)
    best = (None, -np.inf)
    for si in range(starts):
        z0 = (np.concatenate([np.ones(n), 0.1 * np.ones(L)]) if si == 0
              else np.abs(rng.standard_normal(n + L)) + 0.05)
        z0 = z0 / float(cost @ z0)
        I0, _, _, _ = info(z0)
        w0 = np.concatenate([z0, [float(np.min(I0)) - 1e-9]])
        try:
            r = minimize(lambda w: -w[-1], w0,
                         jac=lambda w: np.concatenate([np.zeros(len(w) - 1), [-1.0]]),
                         constraints=cons,
                         bounds=[(1e-10, None)] * (n + L) + [(None, None)],
                         method="SLSQP", options={"maxiter": 800, "ftol": 1e-16})
        except Exception:
            continue
        z = np.maximum(r.x[:-1], 0.0)
        sb = float(cost @ z)
        if sb <= 0:
            continue
        z = z / sb
        I, _, _, _ = info(z)
        v = float(np.min(I))
        if v > best[1]:
            best = (z, v)
    return best


def main():
    print("MASTER: when does a GROUP of calibration queries pay, and each alone not?\n")
    res = {}
    inst, labels, instr = build_instance()

    print("PART 1 -- the ordinary optimum, the active set, and G from the model")
    x, V0 = optimise_ordinary(inst)
    I, K, M, Ki = inst.info(x)
    G, _, T = inst.G(x)
    act = [u for u in range(len(I)) if I[u] <= V0 * (1 + 1e-7)]
    print(f"   ordinary allocation x = {np.round(x,6)}   V_0 = {V0:.9f}")
    print(f"   K = {np.round(K,6).tolist()}   (rank {np.linalg.matrix_rank(K)})")
    print(f"   I_u = {np.round(I,9)}   active set = {act} ({len(act)} of {len(I)})")
    print(f"   G (alternatives x controls), in units of V_0:")
    for u in range(len(I)):
        print(f"      u{u+1} [{labels[u]}]: {np.round(G[u]/V0,6)}")
    res["ordinary"] = {"x": x.tolist(), "V0": V0, "I": I.tolist(),
                       "active_set": act, "G_over_V0": (G / V0).tolist(),
                       "K": K.tolist(), "labels": labels}

    print("\nPART 2 -- single control vs the mixture (the threshold Lambda > V_0)")
    Ga = G[act]
    single = [float(np.min(Ga[:, l])) for l in range(Ga.shape[1])]
    # Lambda = max_rho min_u sum_l rho_l G_ul   (an LP)
    L = Ga.shape[1]
    lp = linprog(np.r_[np.zeros(L), -1.0],
                 A_ub=np.c_[-Ga, np.ones(len(act))], b_ub=np.zeros(len(act)),
                 A_eq=np.array([np.r_[np.ones(L), 0.0]]), b_eq=[1.0],
                 bounds=[(0, None)] * L + [(None, None)], method="highs")
    Lam = float(-lp.fun); rho = lp.x[:L]
    for l in range(L):
        print(f"   control {l+1} alone: min over the active set = "
              f"{single[l]/V0:.6f} V_0  -> derivative {single[l]-V0:+.9f} "
              f"({'HELPS' if single[l] > V0 else 'HURTS'})")
    print(f"   mixture rho = {np.round(rho,6)}: Lambda = {Lam/V0:.6f} V_0 "
          f"-> derivative {Lam-V0:+.9f} ({'HELPS' if Lam > V0 else 'HURTS'})")
    if not (Lam > V0 and all(s < V0 for s in single)):
        raise AssertionError("the construction does not show complementarity")
    print("   => every single control strictly HURTS; the pair strictly HELPS.")
    res["threshold"] = {"single_control_values": single, "Lambda": Lam,
                        "rho": rho.tolist(), "V0": V0,
                        "each_single_hurts": True, "mixture_helps": True}

    print("\nPART 3 -- the derivative formula against a finite difference")
    p3 = []
    for name, rr in (("control 1 only", np.array([1.0, 0.0])),
                     ("control 2 only", np.array([0.0, 1.0])),
                     ("optimal mixture", rho)):
        pred = float(np.min(Ga @ rr)) - V0
        fds = []
        for t in (1e-3, 1e-4, 1e-5):
            a = (1 - t) * x / inst.nu
            Kt = (inst.V * a[:, None]).T @ inst.V
            Kt = Kt + t * (inst.C * (rr / (inst.ckap * inst.cnu))[:, None]).T @ inst.C
            Mt = (inst.d * a[None, :]) @ inst.V
            Dt = 0.5 * (inst.d ** 2 * a[None, :]).sum(1)
            It = Dt - 0.5 * np.einsum('up,pq,uq->u', Mt, np.linalg.pinv(Kt), Mt)
            fds.append((float(np.min(It)) - V0) / t)
        print(f"   {name}: predicted {pred:+.9f}, finite differences "
              + ", ".join(f"{v:+.6f}" for v in fds))
        if abs(fds[-1] - pred) > 1e-3 * max(1.0, abs(pred)):
            raise AssertionError(f"derivative formula fails for {name}")
        p3.append({"direction": name, "predicted": pred, "finite_differences": fds})
    res["derivative_check"] = p3

    print("\nPART 4 -- the p = 1 negative control: mixtures never beat the best single")
    p4 = []
    rng = np.random.default_rng(11)
    worst = 0.0
    for trial in range(400):
        nu_alt, nl = 4, 3
        alpha = np.abs(rng.standard_normal(nu_alt)) + 0.05
        beta = np.abs(rng.standard_normal(nl)) + 0.05
        Gm = np.outer(alpha, beta)              # the p = 1 factorisation
        lp = linprog(np.r_[np.zeros(nl), -1.0],
                     A_ub=np.c_[-Gm, np.ones(nu_alt)], b_ub=np.zeros(nu_alt),
                     A_eq=np.array([np.r_[np.ones(nl), 0.0]]), b_eq=[1.0],
                     bounds=[(0, None)] * nl + [(None, None)], method="highs")
        mix = float(-lp.fun)
        best_single = float(np.max([np.min(Gm[:, l]) for l in range(nl)]))
        worst = max(worst, mix - best_single)
    print(f"   400 random rank-one G: max(mixture - best single) = {worst:.3e}")
    if worst > 1e-9:
        raise AssertionError("a rank-one mixture beat the best single control")
    # and the same instance with a SCALAR nuisance
    V1 = np.ones((4, 1))
    inst1 = Instance(inst.d, V1, inst.nu, inst.cost, np.ones((2, 1)),
                     inst.cnu, inst.ckap)
    x1, V01 = optimise_ordinary(inst1)
    G1, I1, _ = inst1.G(x1)
    act1 = [u for u in range(len(I1)) if I1[u] <= V01 * (1 + 1e-7)]
    rank1 = np.linalg.matrix_rank(G1[act1], tol=1e-9)
    print(f"   the SAME instance with a scalar offset: V_0 = {V01:.9f}, "
          f"G has rank {rank1} -> no complementarity is possible")
    res["negative_control"] = {"max_mixture_minus_best_single": worst,
                               "scalar_nuisance_V0": V01,
                               "scalar_nuisance_G_rank": int(rank1),
                               "scalar_nuisance_G": G1.tolist()}
    p4.append(res["negative_control"])

    print("\nPART 5 -- the full-class optimum, in closed form, with a full dual")
    z, V = full_class_optimum(inst)
    n = len(inst.cost)
    xo, yc = z[:n], z[n:]
    cost = np.concatenate([inst.cost, inst.ckap])
    nuall = np.concatenate([inst.nu, inst.cnu])
    Vall = np.vstack([inst.V, inst.C])
    dall = np.hstack([inst.d, np.zeros((inst.d.shape[0], len(inst.ckap)))])
    a = z / nuall
    Kf = (Vall * a[:, None]).T @ Vall
    Mf = (dall * a[None, :]) @ Vall
    Df = 0.5 * (dall ** 2 * a[None, :]).sum(1)
    Kfi = np.linalg.pinv(Kf)
    Tf = Mf @ Kfi
    If = Df - 0.5 * np.einsum('up,pq,uq->u', Mf, Kfi, Mf)
    actf = [u for u in range(len(If)) if If[u] <= V * (1 + 1e-6)]
    print(f"   primal x = {np.round(xo,6)}, controls = {np.round(yc,6)}, "
          f"V = {V:.9f}   (V_0 = {V0:.9f}, gain {100*(V/V0-1):+.4f}%)")
    print(f"   I_u = {np.round(If,9)}; active {actf}")

    # CLOSED FORM.  By the instance symmetry x_e = x, y_l = y, K = (2x+y) Id and
    # t_u = +- s e_{instr(u)} with s = (x/2)/(2x+y).  With lambda uniform,
    #   H_e/cost_e = [ (1/2 - s)^2 + s^2 ] / 8      (ordinary query)
    #   H_l/kappa  = (s^2/4)/kappa                  (control)
    # and equality of the two forces (1/2 - s)^2 = 2 s^2, i.e. s = (sqrt2 - 1)/2,
    # then y = (sqrt2 - 1) x and V = 3(3 - 2 sqrt2)/32.
    import math as _m
    s_cf = (_m.sqrt(2) - 1) / 2
    V_cf = 3 * (3 - 2 * _m.sqrt(2)) / 32
    x_cf = 1.0 / (4 + (4 / 3) * (_m.sqrt(2) - 1))
    y_cf = (_m.sqrt(2) - 1) * x_cf
    print(f"   closed form: s = (sqrt2-1)/2 = {s_cf:.9f},  x = {x_cf:.9f},  "
          f"y = {y_cf:.9f},  V = 3(3-2 sqrt2)/32 = {V_cf:.9f}")
    if abs(V - V_cf) > 1e-7 * V_cf:
        raise AssertionError(f"solver {V} disagrees with the closed form {V_cf}")
    if max(abs(xo - x_cf).max(), abs(yc - y_cf).max()) > 1e-4:
        raise AssertionError("solver allocation disagrees with the closed form")
    print(f"   full-game gain over ordinary-only: V/V_0 = 18 - 12 sqrt2 = "
          f"{18 - 12*_m.sqrt(2):.9f}")

    # the dual, at the closed-form point, over EVERY ordinary query AND control
    zc = np.concatenate([np.full(n, x_cf), np.full(len(inst.ckap), y_cf)])
    zc = zc / float(cost @ zc)
    ac = zc / nuall
    Kc = (Vall * ac[:, None]).T @ Vall
    Mc = (dall * ac[None, :]) @ Vall
    Tc = Mc @ np.linalg.pinv(Kc)
    lam = np.full(len(If), 1.0 / len(If))
    H = np.array([sum(lam[u] * (dall[u, j] - Vall[j] @ Tc[u]) ** 2
                      for u in range(len(If))) / (2 * nuall[j])
                  for j in range(len(cost))])
    ratio = H / cost
    print(f"   dual lambda = {np.round(lam,6)} (uniform, forced by the symmetry)")
    print(f"   H_e/cost_e over all {len(cost)} queries "
          f"(4 ordinary then 2 controls): {np.round(ratio,10)}")
    print(f"   max = {ratio.max():.10f}, V = {V_cf:.10f}, "
          f"relative excess {ratio.max()/V_cf - 1:+.2e}")
    if ratio.max() > V_cf * (1 + 1e-9):
        raise AssertionError("the dual does not bound every query")
    print("   every ordinary query AND every control is bounded by V, and both")
    print("   kinds are TIGHT -> the primal is optimal over the whole class.")
    res["full_class"] = {"x": xo.tolist(), "controls": yc.tolist(),
                         "V_primal": V, "V_closed_form": V_cf,
                         "s_closed_form": s_cf, "x_closed_form": x_cf,
                         "y_closed_form": y_cf,
                         "V_over_V0": V_cf / V0,
                         "lambda": lam.tolist(),
                         "H_over_cost": ratio.tolist(),
                         "max_H_over_cost": float(ratio.max()),
                         "dual_certifies_every_query": True,
                         "active": actf}

    res["not_established"] = [
        "the active set is read at a numerical tolerance; the threshold theorem is "
        "verified on this instance, not proved for all instances",
        "the full-class optimum is certified by a floating-point primal/dual pair, "
        "not in exact arithmetic",
        "nothing here argues the vector-nuisance model is the right model; the "
        "p = 1 negative control says the earlier common-offset model cannot show "
        "this effect at all",
    ]
    out = REPO / "research/worker_P6_master_20260914/P6_master_group_calibration.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
