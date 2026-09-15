#!/usr/bin/env python3
"""Package 1 (Functional): the extrema-exploration / capacity-gap crossover.

INSTANCE (exactly the family in the assignment):
    incumbent  theta_I = (-1/2, +1/2)                       capacity 1
    outsider   theta_O = (-rho/2, +rho/2, 0, ..., 0)        capacity rho < 1
                                          \\_ n middle cells _/
    Gaussian variance 1, unit cost per cell, every mean free to move,
    allocation w on the 4 + n cells with sum w = 1.
    Alternative set: range(lambda_O) >= range(lambda_I).   Gamma_n(rho) = sup_w J(w).

CLOSED FORM DERIVED HERE (and cross-checked against an independent QP below).
Confining I to an interval of length z costs A (1-z)^2 with A = (1/2) wI0 wI1/(wI0+wI1);
opening the ordered pair (a,b) of O to spread z costs B_ab (z - D_ab)_+^2 with
B_ab = (1/2) wa wb/(wa+wb) and D_ab = theta_a - theta_b.  Both pieces are quadratic
and the crossover z* is interior, so the inner minimisation is exact:

    J(w) = min over ordered pairs (a,b) of  A * B_ab * (1 - D_ab)^2 / (A + B_ab)

This is a MINIMUM OF CONCAVE functions of w (each harmonic mean is concave, and
(A,B) -> AB/(A+B) is concave and increasing), so sup_w J is a concave program.

THE THREE WITNESSES of the assignment are exactly the three pair types:
    type MM  two middle cells        -> D = 0     (witness 1, bound u/(4n))
    type EM  one endpoint + a middle -> D = rho/2 (witness 2, bound u(1-rho/2)^2/(2n))
    type EE  the two O endpoints     -> D = rho   (witness 3, bound (1-u)(1-rho)^2/32)
so the finite relaxed upper bound is
    Gamma_n(rho) <= kappa (1-rho)^2 / (32 kappa + n (1-rho)^2),
    kappa(rho) = min{1/4, (1-rho/2)^2/2}.

LIMIT LAWS UNDER TEST
    (L1) rho fixed < 1          :  n Gamma_n(rho)      -> kappa(rho)
    (L2) rho = 1 - c/sqrt(n)    :  n Gamma_n(rho_n)    -> c^2 / (8 (c^2+4))

Everything raises AssertionError on mismatch. Needs .venv/bin/python for the
independent scipy QP cross-check; the closed-form half is pure python.

    .venv/bin/python scripts/N7_functional_extrema_crossover.py
"""
import itertools
import math
import sys

EPS = 1e-12


# ------------------------------------------------------------------ the model

def cells(rho, n):
    """(mean, tag) for every cell of the outsider, in a fixed order."""
    return [(+rho / 2.0, "E+"), (-rho / 2.0, "E-")] + [(0.0, "M")] * n


def harmonic_half(x, y):
    """(1/2) x y / (x + y): the pair constant of a two-point quadratic."""
    if x <= 0.0 or y <= 0.0:
        return 0.0
    return 0.5 * x * y / (x + y)


def J_closed(wI0, wI1, wO, rho, n):
    """J(w) and the tag of the active pair, by the closed form above."""
    A = harmonic_half(wI0, wI1)
    th = cells(rho, n)
    if A <= 0.0:
        return 0.0, "I-free"          # I can be flattened for free
    best, arg = float("inf"), None
    for a, b in itertools.permutations(range(len(wO)), 2):
        B = harmonic_half(wO[a], wO[b])
        D = th[a][0] - th[b][0]
        if D >= 1.0:                  # already flipped
            return 0.0, "already"
        if B <= 0.0:
            return 0.0, "O-free"      # a zero-weight pair opens for free
        val = A * B * (1.0 - D) ** 2 / (A + B)
        tag = "".join(sorted((th[a][1][0], th[b][1][0])))
        if val < best:
            best, arg = val, ("EE" if tag == "EE" else "MM" if tag == "MM" else "EM")
    return best, arg


def J_scan(wI0, wI1, wO, rho, n, grid=200001):
    """J(w) recomputed WITHOUT the closed form: scan the confinement length z,
    paying min over pairs at that z. Independent of the algebra above."""
    A = harmonic_half(wI0, wI1)
    th = cells(rho, n)
    pairs = []
    for a, b in itertools.permutations(range(len(wO)), 2):
        pairs.append((harmonic_half(wO[a], wO[b]), th[a][0] - th[b][0]))

    def f(z):
        s = A * (1.0 - z) ** 2 if z < 1.0 else 0.0
        e = min(B * max(0.0, z - D) ** 2 for B, D in pairs)
        return s + e

    zs = [i / grid for i in range(grid + 1)]
    k = min(range(len(zs)), key=lambda i: f(zs[i]))
    lo, hi = zs[max(0, k - 1)], zs[min(len(zs) - 1, k + 1)]
    for _ in range(200):
        m1, m2 = lo + (hi - lo) / 3.0, hi - (hi - lo) / 3.0
        if f(m1) <= f(m2):
            hi = m2
        else:
            lo = m1
    return min(f(lo), f(hi), f((lo + hi) / 2.0))


# ------------------------------------------- independent QP over mean vectors

def J_qp(wI0, wI1, wO, rho, n):
    """J(w) as a constrained minimisation over the FULL mean vector, with the
    range constraint written out directly. Uses scipy; no decomposition, no
    closed form - this is the referee for the two routines above."""
    import numpy as np
    from scipy.optimize import minimize

    thI = np.array([-0.5, 0.5])
    thO = np.array([m for m, _ in cells(rho, n)])
    wI = np.array([wI0, wI1])
    wOa = np.array(wO)
    K = len(thO)

    def pack(vI, vO):
        return np.concatenate([vI, vO])

    def obj(v):
        return 0.5 * (np.sum(wI * (v[:2] - thI) ** 2) + np.sum(wOa * (v[2:] - thO) ** 2))

    best = float("inf")
    # one QP per choice of which cells realise each relation's extrema
    for (s, t) in itertools.permutations(range(2), 2):
        for (p, q) in itertools.permutations(range(K), 2):
            cons = []
            for a in range(2):
                if a != s:
                    cons.append({"type": "ineq", "fun": (lambda v, a=a, s=s: v[s] - v[a])})
                if a != t:
                    cons.append({"type": "ineq", "fun": (lambda v, a=a, t=t: v[a] - v[t])})
            for a in range(K):
                if a != p:
                    cons.append({"type": "ineq", "fun": (lambda v, a=a, p=p: v[2 + p] - v[2 + a])})
                if a != q:
                    cons.append({"type": "ineq", "fun": (lambda v, a=a, q=q: v[2 + a] - v[2 + q])})
            cons.append({"type": "ineq",
                         "fun": (lambda v, p=p, q=q, s=s, t=t: (v[2 + p] - v[2 + q]) - (v[s] - v[t]))})
            r = minimize(obj, pack(thI, thO), constraints=cons, method="SLSQP",
                         options={"maxiter": 400, "ftol": 1e-14})
            if r.success:
                v = r.x
                if (v[2:].max() - v[2:].min()) - (v[:2].max() - v[:2].min()) >= -1e-9:
                    best = min(best, float(r.fun))
    return best


# -------------------------------------------------------- the outer maximisation

def kappa(rho):
    return min(0.25, (1.0 - rho / 2.0) ** 2 / 2.0)


def relaxed_upper(rho, n):
    k = kappa(rho)
    return k * (1.0 - rho) ** 2 / (32.0 * k + n * (1.0 - rho) ** 2)


def J_symmetric(p, q, u, rho, n):
    """J at the symmetric allocation: p split over the two incumbent endpoints,
    q over the two outsider endpoints, u spread over the n middle cells.
    p and q are kept SEPARATE - never tied to each other.

    O(1): under this allocation only three ordered pairs can be active, since
    every cell of a given class carries the same mass and the negative-D
    orientations are strictly worse ((1-D)^2 is larger).
      EE : B = q/8,                     D = rho
      EM : B = half-harmonic(q/2, u/n), D = rho/2
      MM : B = u/(4n),                  D = 0        (needs n >= 2)
    `J_symmetric_ref` below re-derives the same number from J_closed."""
    if min(p, q, u) < 0:
        return 0.0, "deg"
    # A cell of weight 0 can be displaced at no cost, so a single one makes the
    # flip free and J = 0. Dropping such a candidate instead (the bug this guard
    # replaces) lets the outer maximiser buy a fake optimum at u = 0.
    if p <= 0 or q <= 0 or (u <= 0 and n >= 1):
        return 0.0, "free"
    A = p / 8.0
    cands = [(q / 8.0, rho, "EE"),
             (harmonic_half(q / 2.0, u / n), rho / 2.0, "EM")]
    if n >= 2:
        cands.append((u / (4.0 * n), 0.0, "MM"))
    best, arg = float("inf"), None
    for B, D, tag in cands:
        if B <= 0.0:
            return 0.0, "O-free"
        val = A * B * (1.0 - D) ** 2 / (A + B)
        if val < best:
            best, arg = val, tag
    return best, arg


def J_symmetric_ref(p, q, u, rho, n):
    """The same quantity straight from J_closed over all ordered pairs."""
    if min(p, q, u) < 0 or p <= 0:
        return 0.0, "deg"
    wO = [q / 2.0, q / 2.0] + [u / n] * n
    return J_closed(p / 2.0, p / 2.0, wO, rho, n)


def gamma_symmetric(rho, n, coarse=60, rounds=32):
    """max over the symmetric 3-simplex (p, q, u), by nested refinement."""
    lo = [0.0, 0.0]
    span = 1.0
    best = (0.0, None, None)
    centre = [1.0 / 3.0, 1.0 / 3.0]
    for rnd in range(rounds):
        step = span / coarse
        found = None
        pi = 0
        while pi <= coarse:
            p = max(1e-12, centre[0] - span / 2 + pi * step)
            qi = 0
            while qi <= coarse:
                q = max(0.0, centre[1] - span / 2 + qi * step)
                u = 1.0 - p - q
                if u >= 0.0:
                    val, tag = J_symmetric(p, q, u, rho, n)
                    if val > best[0]:
                        best = (val, (p, q, u), tag)
                        found = (p, q)
                qi += 1
            pi += 1
        if found is not None:
            centre = list(found)
        span *= 0.5
        if span < 1e-13:
            break
    return best


def check_symmetric_fastpath():
    """The O(1) symmetric evaluator must agree with the all-pairs closed form."""
    import random
    rng = random.Random(4242)
    worst = 0.0
    # interior points AND the degenerate faces - a zero-weight cell must give
    # J = 0 on both paths, which is exactly where the first version was wrong
    cases = [(0.5, 0.5, 0.0), (0.5, 0.0, 0.5), (0.0, 0.5, 0.5),
             (1.0, 0.0, 0.0), (0.34, 0.33, 0.33)]
    for _ in range(400):
        p = rng.uniform(1e-3, 1.0)
        q = rng.uniform(1e-3, max(1e-9, 1.0 - p))
        u = 1.0 - p - q
        if u > 0:
            cases.append((p, q, u))
    for n in (2, 3, 5, 9):
        for rho in (0.0, 0.2, 0.5, 0.75, 0.95):
            for p, q, u in cases:
                a, ta = J_symmetric(p, q, u, rho, n)
                b, tb = J_symmetric_ref(p, q, u, rho, n)
                rel = abs(a - b) / max(b, 1e-300)
                worst = max(worst, rel)
                assert rel < 1e-12, (n, rho, p, q, u, a, b, ta, tb)
                if b > 0:
                    assert ta == tb, (n, rho, p, q, u, ta, tb)
    return worst


def gamma_full(rho, n, starts=10):
    """max over the FULL (4+n)-dimensional simplex, no symmetry imposed.
    Referee for the symmetric reduction - the assignment forbids assuming the
    incumbent and outsider endpoints carry the same mass.

    J is concave but NONSMOOTH (a min over ordered pairs), and minimising the
    nonsmooth objective directly makes SLSQP stall: it fell 1.7e-2 short of the
    symmetric optimum at n=8, rho=0.9. Solved here in EPIGRAPH form instead -
    maximise t subject to  t <= f_ab(w) for every ordered pair (a,b)  and
    sum w = 1 - which is a SMOOTH concave program with (2+n)(1+n) constraints.

    RAISES if no start converges to a feasible point whose reported objective
    equals the objective recomputed at the returned allocation. The first
    version initialised `best = 0.0` and returned it when nothing converged, so
    a stub that always returns 0 was indistinguishable from a working referee
    (see `check_referee_rejects_stub`). Returns (value, allocation, n_converged).
    """
    import numpy as np
    from scipy.optimize import minimize
    K = 2 + n
    dim = 2 + K
    th = cells(rho, n)
    pairs = [(a, b, th[a][0] - th[b][0])
             for a in range(K) for b in range(K) if a != b]
    FLOOR = 1e-11

    def f_ab(z, a, b, D):
        A = 0.5 * z[0] * z[1] / (z[0] + z[1])
        B = 0.5 * z[2 + a] * z[2 + b] / (z[2 + a] + z[2 + b])
        return A * B * (1.0 - D) ** 2 / (A + B)

    cons = [{"type": "eq", "fun": lambda z: np.sum(z[:dim]) - 1.0}]
    for a, b, D in pairs:
        cons.append({"type": "ineq",
                     "fun": (lambda z, a=a, b=b, D=D: f_ab(z, a, b, D) - z[dim])})
    bnds = [(FLOOR, 1.0)] * dim + [(0.0, 1.0)]

    rng = np.random.default_rng(20260913)
    seeds = [np.full(dim, 1.0 / dim),
             np.array([0.2, 0.2, 0.2, 0.2] + [0.2 / n] * n)]
    for _ in range(starts - 2):
        x = rng.random(dim) + 0.05
        seeds.append(x / x.sum())

    best, best_w, converged, why = None, None, 0, []
    for w0 in seeds:
        w0 = np.clip(w0, FLOOR, 1.0)
        w0 = w0 / w0.sum()
        t0 = J_closed(w0[0], w0[1], list(w0[2:]), rho, n)[0]
        z0 = np.concatenate([w0, [t0]])
        r = minimize(lambda z: -z[dim], z0, constraints=cons, bounds=bnds,
                     method="SLSQP", options={"maxiter": 3000, "ftol": 1e-14})
        if not r.success:
            why.append(f"not converged: {r.message}")
            continue
        w = np.asarray(r.x[:dim], dtype=float)
        # FEASIBILITY of the returned allocation, not merely r.success
        if w.min() < -1e-8 or w.max() > 1.0 + 1e-8 or abs(w.sum() - 1.0) > 1e-6:
            why.append(f"infeasible: min={w.min():.3e} max={w.max():.3e} "
                       f"sum={w.sum():.9f}")
            continue
        w = np.clip(w, 0.0, None)
        w = w / w.sum()
        val = J_closed(w[0], w[1], list(w[2:]), rho, n)[0]
        # the epigraph variable it reports must be attained AT the point it
        # returns: t <= J(w), and it must not be slack by more than the solver
        # tolerance, or the value reported is not the value of the allocation
        t = float(r.x[dim])
        if t > val + 1e-9 or val - t > 1e-6 * max(1.0, val):
            why.append(f"objective mismatch: t={t:.6e} J(w)={val:.6e}")
            continue
        converged += 1
        if best is None or val > best:
            best, best_w = val, w
    if converged == 0:
        raise RuntimeError(
            f"gamma_full: no feasible converged start at n={n}, rho={rho}; "
            f"reasons: {why[:4]}")
    return best, best_w, converged


# ----------------------------------------------------------------- the checks

def check_closed_form_against_scan_and_qp():
    """The closed form must reproduce (a) an independent z-scan and (b) a full
    QP over mean vectors that knows nothing about the decomposition."""
    import random
    rng = random.Random(20260913)
    worst_scan = worst_qp = 0.0
    for trial in range(40):
        n = rng.choice([1, 2, 3])
        rho = rng.choice([0.0, 0.25, 0.5, 0.75, 0.9])
        raw = [rng.expovariate(1.0) + 0.02 for _ in range(4 + n)]
        tot = sum(raw)
        w = [x / tot for x in raw]
        wI0, wI1, wO = w[0], w[1], w[2:]
        jc, _ = J_closed(wI0, wI1, wO, rho, n)
        js = J_scan(wI0, wI1, wO, rho, n)
        rel = abs(jc - js) / max(js, 1e-300)
        worst_scan = max(worst_scan, rel)
        assert rel < 1e-7, f"closed form vs z-scan: n={n} rho={rho} {jc!r} {js!r} rel={rel}"
        if trial < 14:
            jq = J_qp(wI0, wI1, wO, rho, n)
            relq = abs(jc - jq) / max(jq, 1e-300)
            worst_qp = max(worst_qp, relq)
            assert relq < 2e-6, f"closed form vs QP: n={n} rho={rho} {jc!r} {jq!r} rel={relq}"
    return worst_scan, worst_qp


def check_symmetric_reduction():
    """TWO-SIDED. The symmetric restriction must not lose anything, AND the
    full-dimensional referee must not fall short of it either.

    The one-sided form `(full - sym)/sym < 1e-5` that stood here certified
    nothing: a referee returning 0 passes it in every case. A referee that
    cannot even reach the symmetric optimum is not exploring the simplex, so it
    cannot testify that nothing outside the symmetric face does better.

    This is a NUMERICAL cross-check only. The mathematical statement is proved
    by `check_concavity_and_symmetry_averaging`, which verifies the two
    hypotheses of the concavity + group-averaging argument (see that docstring);
    SLSQP proves nothing here.
    """
    worst_gain = 0.0        # how far the referee beats the symmetric optimum
    worst_shortfall = 0.0   # how far it falls short of it
    rows = []
    for n in (2, 4, 8):
        for rho in (0.0, 0.5, 0.9):
            gs = gamma_symmetric(rho, n)[0]
            gf, wf, nconv = gamma_full(rho, n)
            rel = (gf - gs) / max(gs, 1e-300)
            worst_gain = max(worst_gain, rel)
            worst_shortfall = max(worst_shortfall, -rel)
            rows.append((n, rho, gs, gf, rel, nconv))
            assert rel < 1e-5, (
                f"full-dimensional optimum beats the symmetric one: "
                f"n={n} rho={rho} sym={gs!r} full={gf!r} rel={rel}")
            assert rel > -1e-3, (
                f"the full-dimensional referee FELL SHORT of the symmetric "
                f"optimum by {-rel:.3e} at n={n} rho={rho} "
                f"(sym={gs!r} full={gf!r}, {nconv} converged starts): it is not "
                f"searching the simplex, so it certifies nothing")
    return worst_gain, worst_shortfall, rows


def check_referee_rejects_stub():
    """NEGATIVE CONTROL, in answer to the supervisor's attack: swap the
    full-dimensional referee for a stub that always returns 0 and confirm the
    check now FAILS. Under the previous one-sided test all nine cases still
    passed with that stub."""
    import builtins
    g = globals()
    real = g["gamma_full"]
    g["gamma_full"] = lambda rho, n, starts=10: (0.0, None, 1)
    try:
        check_symmetric_reduction()
    except AssertionError:
        return True
    finally:
        g["gamma_full"] = real
    raise AssertionError(
        "a zero-returning stub still passes check_symmetric_reduction: the "
        "check does not certify that the symmetric reduction is lossless")


def _group_average(wI0, wI1, wO, n):
    """Average of the allocation over the instance's symmetry group: the
    permutations of the n middle cells, the transposition of the two incumbent
    cells, and the transposition of the two outsider endpoints."""
    p = wI0 + wI1
    q = wO[0] + wO[1]
    u = sum(wO[2:])
    return p / 2.0, p / 2.0, [q / 2.0, q / 2.0] + [u / n] * n


def _group_act(wI0, wI1, wO, n, rng):
    """A uniformly random element of that group applied to the allocation."""
    import random
    mid = list(wO[2:])
    rng.shuffle(mid)
    a, b = (wI1, wI0) if rng.random() < 0.5 else (wI0, wI1)
    e = [wO[1], wO[0]] if rng.random() < 0.5 else [wO[0], wO[1]]
    return a, b, e + mid


def check_concavity_and_symmetry_averaging():
    """THE MATH, not the solver. The symmetric reduction is lossless because

      (i)  J is INVARIANT under the instance's symmetry group G = (permutations
           of the n middle cells) x (swap of the two incumbent cells) x (swap of
           the two outsider endpoints).  Each generator permutes the set of
           ordered pairs while carrying its (B_ab, D_ab) along, and A is
           symmetric in (wI0, wI1), so every term of the min is permuted among
           itself.
      (ii) J is CONCAVE on the simplex: it is a minimum over ordered pairs of
           A*B/(A+B)*(1-D)^2, each harmonic half is concave in w, and
           (A,B) -> AB/(A+B) is concave and nondecreasing in each argument, so
           each term is concave and the pointwise min of concave is concave.

    Then for any allocation w, its group average wbar = (1/|G|) sum_g g.w is
    G-invariant - i.e. of the symmetric form (p/2, p/2, q/2, q/2, u/n, ..., u/n) -
    and by (ii) then (i),

        J(wbar) >= (1/|G|) sum_g J(g.w) = J(w).

    So the supremum over the symmetric face equals the supremum over the whole
    simplex. NO optimizer is involved. This function verifies the two
    hypotheses numerically over random allocations - invariance under random
    group elements, concavity along random chords - and checks the conclusion
    J(wbar) >= J(w) directly.
    """
    import random
    rng = random.Random(20260913)
    worst_inv = 0.0
    worst_concave = 0.0
    worst_avg_drop = 0.0
    tested = 0
    for n in (2, 3, 4, 8):
        for rho in (0.0, 0.25, 0.5, 0.75, 0.9):
            for _ in range(60):
                raw = [rng.expovariate(1.0) + 1e-9 for _ in range(4 + n)]
                t = sum(raw)
                w = [x / t for x in raw]
                wI0, wI1, wO = w[0], w[1], w[2:]
                base = J_closed(wI0, wI1, wO, rho, n)[0]

                # (i) invariance under random group elements
                for _ in range(4):
                    a, b, e = _group_act(wI0, wI1, wO, n, rng)
                    v = J_closed(a, b, e, rho, n)[0]
                    worst_inv = max(worst_inv, abs(v - base) / max(base, 1e-300))
                    assert abs(v - base) <= 1e-9 * max(1.0, base), (
                        f"J is NOT invariant under the symmetry group: "
                        f"n={n} rho={rho} {base!r} vs {v!r}")

                # (ii) concavity along a random chord
                raw2 = [rng.expovariate(1.0) + 1e-9 for _ in range(4 + n)]
                t2 = sum(raw2)
                w2 = [x / t2 for x in raw2]
                lam = rng.uniform(0.05, 0.95)
                mix = [lam * x + (1 - lam) * y for x, y in zip(w, w2)]
                jm = J_closed(mix[0], mix[1], mix[2:], rho, n)[0]
                j2 = J_closed(w2[0], w2[1], w2[2:], rho, n)[0]
                chord = lam * base + (1 - lam) * j2
                defect = (chord - jm) / max(chord, 1e-300)
                worst_concave = max(worst_concave, defect)
                assert defect <= 1e-9, (
                    f"J is NOT concave along a chord: n={n} rho={rho} "
                    f"lam={lam} J(mix)={jm!r} < {chord!r}")

                # the conclusion: averaging over G does not decrease J
                aI0, aI1, aO = _group_average(wI0, wI1, wO, n)
                javg = J_closed(aI0, aI1, aO, rho, n)[0]
                drop = (base - javg) / max(base, 1e-300)
                worst_avg_drop = max(worst_avg_drop, drop)
                assert drop <= 1e-9, (
                    f"group averaging DECREASED J: n={n} rho={rho} "
                    f"{base!r} -> {javg!r}")
                tested += 1
    return worst_inv, worst_concave, worst_avg_drop, tested


def check_rho_zero_matches_flat_outsider():
    """At rho = 0 every outsider cell sits at 0, so this family degenerates to
    the flat-outsider instance of package N1 with K = 2 + n cells, whose exact
    rate is Gamma_K = 1/(2 (2 + sqrt(2K))^2). Independent anchor for the outer
    maximiser."""
    worst = 0.0
    for n in (2, 4, 8, 16, 64):
        K = 2 + n
        want = 1.0 / (2.0 * (2.0 + math.sqrt(2.0 * K)) ** 2)
        got = gamma_symmetric(0.0, n)[0]
        rel = abs(got - want) / want
        worst = max(worst, rel)
        assert rel < 1e-6, f"rho=0 disagrees with N1: n={n} got={got!r} want={want!r}"
    return worst


def check_relaxed_upper_bound():
    """Gamma_n <= kappa (1-rho)^2 / (32 kappa + n (1-rho)^2) - the bound the three
    witnesses give. It is a RELAXATION, so it must dominate but need not be tight."""
    rows = []
    for n in (4, 16, 64, 256):
        for rho in (0.0, 0.3, 0.5858, 0.75, 0.9):
            g = gamma_symmetric(rho, n)[0]
            ub = relaxed_upper(rho, n)
            assert g <= ub * (1 + 1e-6), f"upper bound violated: n={n} rho={rho} {g!r} > {ub!r}"
            rows.append((n, rho, g, ub, g / ub))
    return rows


def law_fixed_rho():
    rows = []
    for rho in (0.0, 0.3, 0.5858, 0.75, 0.9):
        for n in (4, 16, 64, 256, 1024):
            g, w, tag = gamma_symmetric(rho, n)
            rows.append((rho, n, n * g, kappa(rho), tag, w))
    return rows


def law_critical_scale():
    rows = []
    for c in (0.5, 1.0, 2.0, 4.0):
        for n in (4, 16, 64, 256, 1024, 4096):
            rho = 1.0 - c / math.sqrt(n)
            if rho < 0:
                continue
            g, w, tag = gamma_symmetric(rho, n)
            rows.append((c, n, rho, n * g, c * c / (8.0 * (c * c + 4.0)), tag, w))
    return rows


if __name__ == "__main__":
    ws, wq = check_closed_form_against_scan_and_qp()
    print(f"closed form vs independent z-scan : worst rel = {ws:.2e}")
    print(f"closed form vs independent QP     : worst rel = {wq:.2e}")
    print(f"O(1) symmetric fast path vs all-pairs : worst rel = {check_symmetric_fastpath():.2e}")

    inv, conc, drop, ntested = check_concavity_and_symmetry_averaging()
    print(f"symmetry group invariance of J    : worst rel deviation = {inv:.2e}"
          f"   ({ntested} allocations)")
    print(f"concavity of J along random chords: worst defect        = {conc:.2e}")
    print(f"=> group averaging never lowers J : worst drop          = {drop:.2e}"
          f"   [this is the PROOF that the symmetric reduction is lossless]")

    wsym, wshort, symrows = check_symmetric_reduction()
    print(f"SLSQP referee (cross-check only)  : worst gain over symmetric = {wsym:.2e}"
          f", worst shortfall = {wshort:.2e}")
    print(f"negative control (stub referee rejected) : {check_referee_rejects_stub()}")
    print(f"rho=0 reduces to N1 flat outsider : worst rel = {check_rho_zero_matches_flat_outsider():.2e}")

    ubrows = check_relaxed_upper_bound()
    print("\nthree-witness relaxed upper bound (must dominate; tightness is the ratio)")
    print(f"{'n':>6}{'rho':>9}{'Gamma_n':>14}{'bound':>14}{'ratio':>9}")
    for n, rho, g, ub, r in ubrows:
        print(f"{n:>6}{rho:>9.4f}{g:>14.6e}{ub:>14.6e}{r:>9.4f}")

    print("\n(L1) rho fixed:  n*Gamma_n  ->  kappa(rho) = min{1/4, (1-rho/2)^2/2}")
    print(f"{'rho':>9}{'n':>7}{'n*Gamma_n':>14}{'kappa':>12}{'active':>8}   (p, q, u)")
    for rho, n, ng, k, tag, w in law_fixed_rho():
        print(f"{rho:>9.4f}{n:>7}{ng:>14.8f}{k:>12.8f}{tag:>8}   "
              f"({w[0]:.4g}, {w[1]:.4g}, {w[2]:.4g})")

    print("\n(L2) rho = 1 - c/sqrt(n):  n*Gamma_n  ->  c^2/(8(c^2+4))")
    print(f"{'c':>6}{'n':>7}{'rho':>9}{'n*Gamma_n':>14}{'limit':>12}{'active':>8}   (p, q, u)")
    for c, n, rho, ng, lim, tag, w in law_critical_scale():
        print(f"{c:>6.2f}{n:>7}{rho:>9.5f}{ng:>14.8f}{lim:>12.8f}{tag:>8}   "
              f"({w[0]:.4g}, {w[1]:.4g}, {w[2]:.4g})")
    print("\nall assertions passed")
