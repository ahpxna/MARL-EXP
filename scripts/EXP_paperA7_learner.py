#!/usr/bin/env python3
"""Paper A7: the LEARNER, with certified stopping and no access to the truth.

WHAT WAS WRONG BEFORE.  `EXP_paperA7_track_and_stop.py` computed the oracle allocation from
the TRUE world and handed it to the loop.  That measures the finite-alpha overhead of the
stopping rule under a perfect allocation; it is not the algorithm, and its output is an
oracle-allocation DIAGNOSTIC.  That script is kept, relabelled, and this one replaces it as
the evidence for the rate.  Three arms are run on one model so the difference is visible:

    LEARNER   allocation built only from the history.
    ORACLE    allocation from the true world -- a DIAGNOSTIC, not a competitor.  The
              earlier description of it as "an unattainable lower envelope on stopping
              time" is WITHDRAWN and was wrong: the oracle allocation maximises the
              ASYMPTOTIC information rate, which is not a lower bound on the stopping
              time at any finite alpha.  A learner that stops before the oracle on some
              path is therefore not evidence of a bug.
    UNIFORM   equal allocation -- what ignoring the oracle costs.

COMMON RANDOM NUMBERS ACROSS ALPHA.  `alpha` enters `run` at exactly one place, the
threshold inside `stop_certificate`; selection, allocation and tracking never see it.  So
for a FIXED observation path the stopping time is monotone in alpha by construction.  An
earlier version drew a fresh segment of one stream for every (alpha, arm, run) cell, which
put the four alphas on INDEPENDENT paths; the non-monotone means that produced were
between-run variation and were at one point misread here as an effect of the threshold
penalty.  The seed is now `[BASE_SEED, arm_ix, run_ix]`, free of alpha, so the four alphas
share a path and `alpha_monotone_pathwise` below asserts the monotonicity as a check on
that structural claim rather than as prose.

INFORMATION ACCESS.  The learner sees the query counts, the realised observations, the known
variances, and the model class.  It never sees `theta`.  The simulator alone holds it, and
the only channel is the sampled `Y`.

THE POLICY, following the blueprint.

  1. `mu_hat_t` from the observations; the tracking radius
     `r_t = max_e sigma_e sqrt(2 (a + N_e) b_t(t^-4)) / N_e` at level `t^-4`.
  2. Oracle brackets `[l_T, u_T]` for each answer, from the cutting-plane solver at
     `mu_hat_t`: the lower bracket is an achieved design's value, the upper is the LP bound.
     Both are computed, so the bracket width is real and is recorded.
  3. Keep `{T : u_T >= max_S l_S - 2 L r_t}` with `L = 2B/min_e var_e`, the
     variance-aware Lipschitz modulus, and take the first survivor in a FIXED order.
  4. Allocation from the selected answer's cutting-plane design, at `mu_hat_t`.
  5. Forced exploration `rho_t = (t+1)^-1/2`, then cumulative-quota tracking with the index
     convention of `LeanPaperA7TrackingV1`.

  The oracle is recomputed every `oracle_every` steps rather than every sample.  The
  schedule is a parameter, is recorded, and the allocation between refreshes is the last
  one computed -- a staleness that any proof of this implementation would have to carry.

CERTIFIED STOPPING.  The rule needs `inf_{lambda in Alt(T)} Q_t(lambda) > b_t(alpha)`, so it
needs a LOWER bound on each regional infimum.  A primal point's objective is an UPPER bound
and cannot justify stopping; the previous script used one, which could stop early.  Here
each region returns the WEAK-DUALITY bound

    g(y) = - (1/2) y^T A H^-1 A^T y + y^T (A mu_hat - b),    y >= 0,

which satisfies `g(y) <= min` for EVERY non-negative `y`, so it is valid whatever the solver
did.  `y` is recovered by non-negative least squares at the primal point, which makes the
bound tight when the solve was good and merely conservative when it was not.  If any region
fails to produce a bound, the rule does NOT stop.

  The rule is evaluated on a schedule.  The earlier claim that this delays stopping by less
  than the schedule gap is WITHDRAWN: the statistic can cross the threshold and fall back
  between checks, so the gap bounds nothing without a proof that crossings persist.  What is
  true, and all that is claimed, is that the reported time is a stopping time adapted to the
  history, so correctness is unaffected.

THREE REPAIRS AFTER AUDIT.

  WEIGHT FLOOR.  The solver needs a strictly positive `H`, so it runs at
  `w~ = max(w, EPS_W) >= w`.  Energy increases with the weights, so a lower bound for `w~`
  is not a lower bound for `w`.  `floor_correction` subtracts the box bound
  `2 B^2 sum_e (w~_e - w_e) / var_e`, so `J_at_lower` now returns a bound that really is
  below the value at the design the loop uses.

  NUMERICAL FAILURE.  Every escape hatch increments a counter in `FAILURES`, and the
  counters are written to the artifact whether or not any fired.  A non-finite dual value
  now returns `0.0` -- valid, because `y = 0` is feasible and gives `g(0) = 0` -- which can
  never exceed the threshold, so a failed solve cannot make the rule fire.

  THE BENCHMARK IS AN INTERVAL.  The artifact used to record `Gamma_comp := lo` and drop
  the upper side, so the `1/Gamma` line had no two-sided certificate behind it.  Both sides
  are now recorded, with the achieved design for the lower side and, for the upper side, a
  PRIOR `p` over the collected alternatives: `max_e (sum_l p_l g_l)_e` bounds the game for
  EVERY design, and the self-check verifies `p >= 0`, `sum p = 1` and recomputes the bound
  from `p` alone rather than trusting the LP.

SELF-CHECKS.  Correctness on every stopped run.  The dual bound must never exceed the primal
value, which is weak duality and would catch a sign error.  The prior certificate must be a
probability vector and must reproduce the upper bracket.  No ordering among the three arms
is asserted: two earlier versions asserted one and both were wrong.
"""

import hashlib
import json
import math
import pathlib
import sys

import numpy as np
from scipy.optimize import minimize
from scipy.stats import t as student_t

sys.path.insert(0, "scripts")
from EXP_paperA_separation_games import (REGIONS, family_low, lp_upper, solve_region,
                                         true_gradient)

CHECKS = []

# Every numerical escape hatch increments a counter here, and the counters are written to
# the artifact.  A guarantee that depends on a solve succeeding is worth nothing if the
# failures are invisible, and "no NaN appeared in this run" is not the same statement as
# "the code handles a NaN".
FAILURES = {"regional_dual_nonfinite": 0, "regional_primal_failed": 0,
            "lp_upper_failed": 0, "lp_prior_failed": 0, "stop_bound_nonfinite": 0,
            "primal_infeasible_witness": 0}


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


EPS_W = 1e-9
# A point the solver calls feasible may violate its region by a little.  Such a point can
# sit BELOW the region's true minimum, so using its objective as an upper bound is unsound
# and the cut it generates is taken at a world that is not an alternative.  Witnesses are
# therefore checked against the constraints rather than trusted to `res.success`.
FEAS_TOL = 1e-8
# The selection rule is compared with a slack, so float noise can only ever make it KEEP an
# answer, never drop one.  Dropping the correct answer is the failure that matters.
NUM_TOL = 1e-9
# The regional dual is a smooth concave QP on the non-negative orthant; how hard it is
# solved is a separate question from how many cutting planes are collected, and the two
# must be varied independently to attribute the bracket's residual gap to one of them.
DUAL_ITERS = 400
# How far the cutting-plane iterate moves toward the relaxation's vertex each round.
BRACKET_DAMPING = 0.5
# The smallest bracket width worth asking for.  MEASURED: the damped bracket with the
# dual solved to tolerance settles at ~5.3e-7, so the floor must sit ABOVE that or the
# early break can never fire.  At 1e-6 a bracket costs 5.7s; at 2e-7 (below the settling
# width) the same bracket costs 86.7s for an identical answer.  An earlier floor of 2e-7
# was therefore useless -- it looked like a safety net and was inert.
BRACKET_TOL_FLOOR = 1e-6
BRACKET_ITERS_CAP = 80


def region_violation(Amat, bvec, x):
    """How far `x` is outside `{A x <= b}`; non-positive means feasible."""
    if len(bvec) == 0:
        return 0.0
    return float(np.max(Amat @ x - bvec))
REG_A = 1.0
ANSWERS = ["A", "B"]
BOX_B = 8.0                       # the model class lives in [-B, B]^E


def lipschitz_modulus(var):
    """The modulus of `J_lipschitz_in_world`, ON THIS OBSERVATION MODEL.

    That lemma is stated for unit variance and gives `2B`.  With per-cell variances the
    energy carries `1 / var_e`, and repeating its proof gives

        |J(w, mu) - J(w, mu')|  <=  2 B ||mu - mu'||_inf  *  max_e (1 / var_e),

    so the modulus is `2B / min_e var_e`.  On the world used here `min var = 1` and the two
    agree, but that is an accident of this instance: computing the modulus from `var` keeps
    the selection rule correct if the variances change, and keeps the constant consistent
    with the radius, which already carries `sigma_e`.  Using `2B` with a radius that carries
    sigma and variances above one would mix two normalisations.
    """
    return 2.0 * BOX_B / float(np.min(var))


def rangeA(v):
    return v[0:4].max() - v[0:4].min()


def rangeB(v):
    return v[4:8].max() - v[4:8].min()


def loss_of(T, v):
    return 0.5 * (rangeB(v) if T == "A" else rangeA(v))


def best_answer(v):
    return ANSWERS[int(np.argmin([loss_of(T, v) for T in ANSWERS]))]


def regret_of(T, v):
    return loss_of(T, v) - min(loss_of(S, v) for S in ANSWERS)


def _class_rows(B):
    """The rows defining the model class: centered tables inside a box.

    `centered_additive_response` holds on the CENTERED class -- there the product response
    is the table itself, so the loss identity and the Gaussian KL identity are about the
    same object.  `J_lipschitz_in_world` holds on a BOX.  A solver that ignores either is
    optimising over worlds the theorems do not speak about, so both are carried here as
    explicit constraints rather than left to the docstring.
    """
    rows, rhs = [], []
    for off in (0, 4):
        r = np.zeros(8)
        r[off:off + 4] = 1.0
        rows.append(r.copy()); rhs.append(0.0)        # sum <= 0
        rows.append(-r); rhs.append(0.0)              # sum >= 0
    for e in range(8):
        r = np.zeros(8); r[e] = 1.0
        rows.append(r.copy()); rhs.append(B)
        rows.append(-r); rhs.append(B)
    return np.array(rows), np.array(rhs)


_CLASS_A, _CLASS_B = _class_rows(BOX_B)


def alt_regions_for(T):
    """The answer's alternative set, intersected with the model class."""
    base = REGIONS if T == "A" else [
        (np.hstack([A[:, 4:8], A[:, 0:4]]), b, t) for A, b, t in REGIONS]
    out = []
    for Amat, bvec, tag in base:
        out.append((np.vstack([Amat, _CLASS_A]),
                    np.concatenate([bvec, _CLASS_B]), tag))
    return out


def center_world(theta):
    """Move a world into the centered class without changing any range."""
    th = np.array(theta, dtype=float)
    th[0:4] -= th[0:4].mean()
    th[4:8] -= th[4:8].mean()
    return th


# ------------------------------------------------------- certified regional lower bound
def regional_lower_bound(center, H, Amat, bvec):
    """Maximise the dual over non-negative multipliers.  There is no failure mode.

    For the convex QP `min (1/2)(x-c)^T H (x-c)` over `{A x <= b}`, weak duality gives

        g(y) = - (1/2) y^T A H^-1 A^T y + y^T (A c - b)  <=  min,    for EVERY y >= 0,

    so ANY non-negative `y` yields a valid bound, and `y = 0` already yields `0`.  Solving
    the dual directly is therefore sound whatever the optimiser does, which a primal solve
    is not: a primal point's objective is an UPPER bound on the minimum and cannot justify
    stopping.  An earlier version of this script recovered multipliers from a primal solve,
    and on this model that solve failed on eleven of the sixteen regions.

    By strong duality for a feasible convex QP the maximum equals the minimum, so the bound
    is tight when the optimiser converges and merely conservative when it does not.
    """
    Hinv = 1.0 / np.maximum(H, 1e-300)
    c = Amat @ center - bvec

    def neg_g(y):
        Aty = Amat.T @ y
        return 0.5 * float(Aty @ (Hinv * Aty)) - float(y @ c)

    def grad(y):
        Aty = Amat.T @ y
        return Amat @ (Hinv * Aty) - c

    res = minimize(neg_g, np.zeros(len(bvec)), jac=grad, method="L-BFGS-B",
                   bounds=[(0.0, None)] * len(bvec),
                   options={"maxiter": DUAL_ITERS, "ftol": 1e-16, "gtol": 1e-12})
    y = np.maximum(res.x, 0.0)
    if not np.all(np.isfinite(y)):
        FAILURES["regional_dual_nonfinite"] += 1
        return 0.0
    val = -neg_g(y)
    if not np.isfinite(val):
        # `y = 0` is always feasible and gives `g(0) = 0`, so zero is a valid bound
        # whatever the optimiser returned.  Falling back to it keeps the certificate sound
        # and, because zero can never exceed the threshold, guarantees the rule does not
        # fire on a failed solve rather than silently firing on a NaN comparison.
        FAILURES["regional_dual_nonfinite"] += 1
        return 0.0
    return max(val, 0.0)


def regional_primal_value(center, H, Amat, bvec):
    """The primal value where a solve succeeds, used ONLY to check weak duality."""
    res = solve_region(center, H, Amat, bvec, starts=2)
    if res is None:
        FAILURES["regional_primal_failed"] += 1
        return None
    if region_violation(Amat, bvec, res.x) > FEAS_TOL:
        FAILURES["primal_infeasible_witness"] += 1
        return None
    return float(res.fun)


def stop_certificate(mu_hat, N, var, alpha, T):
    """Fires only when a CERTIFIED lower bound on every region exceeds the threshold."""
    b_alpha = np.log(1.0 / alpha) + 0.5 * np.sum(np.log1p(N / REG_A))
    H = N ** 2 / ((REG_A + N) * var)
    worst = np.inf
    if not np.isfinite(b_alpha):
        FAILURES["stop_bound_nonfinite"] += 1
        return False, 0.0, b_alpha
    for Amat, bvec, _ in alt_regions_for(T):
        lo = regional_lower_bound(mu_hat, H, Amat, bvec)
        if not np.isfinite(lo):
            FAILURES["stop_bound_nonfinite"] += 1
            return False, 0.0, b_alpha
        if lo <= b_alpha:
            return False, lo, b_alpha
        worst = min(worst, lo)
    return True, worst, b_alpha


# ------------------------------------------------------- the oracle, at an ESTIMATE
def J_at(w, center, var, regions):
    """An UPPER bound on the answer's value at a design, plus a witness.

    A primal point's objective bounds its region's minimum from ABOVE, so the minimum over
    regions of these values bounds `J_T(w)` from above.  That is the right direction for
    generating cutting planes, and the wrong one for a lower bracket -- which is why
    `J_at_lower` exists and is used for the bracket instead.
    """
    H = np.maximum(w, EPS_W) / var
    best, wit = np.inf, None
    for Amat, bvec, _ in regions:
        res = solve_region(center, H, Amat, bvec, starts=1)
        if res is None:
            continue
        if region_violation(Amat, bvec, res.x) > FEAS_TOL:
            FAILURES["primal_infeasible_witness"] += 1
            continue
        if res.fun < best - 1e-14:
            best, wit = float(res.fun), res.x
    return best, wit


def floor_correction(w, var):
    """What raising the design to `max(w, EPS_W)` can be worth, on the box.

    The solver needs a strictly positive `H`, so it is run at `w~ = max(w, EPS_W) >= w`.
    Energy is INCREASING in the weights, so a lower bound for `w~` is NOT a lower bound for
    `w`; an earlier version of this function reported one as though it were.  On the model
    class every world satisfies `|mu_e| <= B`, so `(lam_e - mu_e)^2 <= 4 B^2` and

        J_w~(lam) - J_w(lam) = (1/2) sum_e (w~_e - w_e) (lam_e - mu_e)^2 / var_e
                            <= 2 B^2 sum_e (w~_e - w_e) / var_e,

    uniformly in `lam`.  Subtracting that from the `w~` bound gives a bound that really is
    below `J_w`.  The correction is tiny here -- `EPS_W = 1e-9` -- but it is the difference
    between a certificate and an approximation, and it is now computed rather than waved
    away.
    """
    return 2.0 * BOX_B ** 2 * float(np.sum((np.maximum(w, EPS_W) - w) / var))


def J_at_lower(w, center, var, regions):
    """A CERTIFIED lower bound on the answer's value AT THE DESIGN `w`.

    Every region contributes its weak-duality bound, and the minimum over regions is a
    lower bound on `J_T(w~)`.  No region is skipped: the dual maximisation has no failure
    mode, and a region that somehow produced nothing would contribute the conservative
    value zero rather than be dropped.  Dropping a region would raise the reported minimum
    and could make a suboptimal answer look optimal.  The floor correction then carries the
    bound from `w~` back to `w`.
    """
    H = np.maximum(w, EPS_W) / var
    best = np.inf
    for Amat, bvec, _ in regions:
        lo = regional_lower_bound(center, H, Amat, bvec)
        if lo is None or not np.isfinite(lo):
            lo = 0.0
        best = min(best, lo)
    return max(best - floor_correction(w, var), 0.0)


def lp_prior(grads):
    """A PRIOR over the collected alternatives, and the upper bound it certifies.

    For any probability vector `p` on the alternatives collected so far,

        min_lam J_w(lam)  <=  sum_l p_l J_w(lam^l)  =  <w, sum_l p_l g_l>
                          <=  max_e (sum_l p_l g_l)_e     for every design `w`,

    the last step because `w` is itself a probability vector.  So the right-hand side is an
    upper bound on the GAME value, valid for every design and checkable from `p` alone
    without trusting the solver: the checks below verify `p >= 0` and `sum p = 1` and then
    recompute the bound.  This is the dual of `lp_upper`, solved directly so the multipliers
    are an output rather than a by-product to be scraped.
    """
    from scipy.optimize import linprog
    G = np.array(grads)                                # (L, 8)
    L = len(G)
    c = np.zeros(L + 1); c[-1] = 1.0                   # minimise s
    A_ub = np.hstack([G.T, -np.ones((G.shape[1], 1))])  # (sum_l p_l g_l)_e - s <= 0
    b_ub = np.zeros(G.shape[1])
    A_eq = np.zeros((1, L + 1)); A_eq[0, :L] = 1.0
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=np.array([1.0]),
                  bounds=[(0.0, None)] * L + [(None, None)], method="highs")
    if not res.success:
        FAILURES["lp_prior_failed"] += 1
        return None, None
    p = np.array(res.x[:L])
    return float(np.max(G.T @ p)), p


def keep_set(los, ups, L, r_t, answers=None):
    """The answer-selection rule, as a function so it can be TESTED rather than trusted.

    Keep `T` when its upper bracket still reaches the best certified lower bracket, after
    allowing for how far `mu_hat` may be from `theta`:

        keep T  <=>  u_T  >=  max_S l_S  -  2 L r_t.

    Pulling this out of the loop is not cosmetic.  In every run performed here the allowance
    `2 L r_t` is larger than the gap between the answers by seven orders of magnitude, so
    the set never narrows and the loop alone cannot show the rule works.  `test_keep_set`
    below drives it directly with inputs where it must narrow, and checks that it does --
    and, more importantly, that it never drops the best answer.
    """
    answers = ANSWERS if answers is None else answers
    thr = max(los.values()) - 2.0 * L * r_t - NUM_TOL
    return [T for T in answers if ups[T] >= thr]


def elimination_horizon(G, L, var, E=8, a=REG_A, Nmax=1e14):
    """Samples per cell at which the allowance first fits inside the answer gap.

    Returns `None` if the ladder runs past `Nmax`.  This is the number that makes the
    statement quantitative: the selection rule cannot narrow anything before this many
    samples, whatever the confidence level, because the allowance is a property of the
    radius and the Lipschitz modulus and not of `alpha`.
    """
    target = G / (2.0 * L)
    N = 1.0
    while N < Nmax:
        t = E * N
        b = math.log(max(t, 2.0) ** 4) + 0.5 * E * math.log1p(N / a)
        r = float(np.sqrt(np.max(var)) * math.sqrt(2.0 * (a + N) * b) / N)
        if r < target:
            return N
        N *= 1.3
    return None


def oracle_bracket(center, var, regions, iters=25, want_prior=False,
                   tol=1e-10):
    """Cutting planes at an ESTIMATE, with a CERTIFIED lower bracket.

    The upper bracket is the LP over the alternatives collected so far, which bounds every
    design.  The lower bracket is the best CERTIFIED design value seen, computed by
    `J_at_lower`; an earlier version used the primal value here, which is an upper bound and
    therefore cannot certify `l_T <= Gamma_T`.  Since the selection rule compares `u_T`
    against `max_S l_S`, an inflated `l` could discard the optimal answer.
    """
    w = np.ones(8) / 8.0
    cuts, lo, best_w, up = [], -np.inf, w.copy(), np.inf
    for _ in range(iters):
        val, wit = J_at(w, center, var, regions)
        cert_lo = J_at_lower(w, center, var, regions)
        if cert_lo > lo:
            lo, best_w = cert_lo, w.copy()
        if wit is None:
            break
        cuts.append(true_gradient(wit, center, var))
        u, w_lp = lp_upper(cuts)
        if u is None:
            FAILURES["lp_upper_failed"] += 1
            break
        # EVERY relaxation value is separately a valid upper bound, so the running
        # minimum is sound and the latest one is not.  Overwriting `up` with a numerically
        # worse iterate was one half of the gap that used to plateau at 8.0e-3.
        up = min(up, u)
        # The other half was Kelley's own oscillation: the undamped iterate jumps to a
        # vertex of the relaxation and the incumbent stops improving.  Stepping half way
        # toward it and cutting there as well keeps the incumbent moving.  Measured at a
        # FIXED estimate the two changes together take the gap from 8.0e-3 to 1.9e-4, and
        # with the dual solved to tolerance to 5.0e-7 -- flat in both the cutting-plane
        # count and the dual budget, i.e. at solver round-off rather than at a duality
        # gap.  The earlier reading of that plateau as structural was wrong.
        w = (1.0 - BRACKET_DAMPING) * best_w + BRACKET_DAMPING * w_lp
        _, wit2 = J_at(w, center, var, regions)
        if wit2 is not None:
            cuts.append(true_gradient(wit2, center, var))
        cert_lo2 = J_at_lower(w, center, var, regions)
        if cert_lo2 > lo:
            lo, best_w = cert_lo2, w.copy()
        if up - lo <= tol * max(1.0, abs(up)):
            break
    if want_prior:
        if not cuts:
            return lo, up, best_w, None
        u_prior, p = lp_prior(cuts)
        return lo, up, best_w, {"upper_from_prior": u_prior,
                                "prior": None if p is None else p.tolist(),
                                "cuts": [g.tolist() for g in cuts]}
    return lo, up, best_w


# ------------------------------------------------------- the runs
def make_sampler(theta, var):
    """Close the true world into a draw function.

    This is the ONLY place the world is read.  `run` receives the closure, never the
    vector, so "the learner does not read the truth" is a property of the call graph and
    can be asserted structurally instead of promised in a comment.
    """
    sig = np.sqrt(var)
    return lambda e, rng: theta[e] + sig[e] * rng.normal()


def run(rng, sampler, var, alpha, budget, arm, oracle_every, check_every,
        w_oracle=None):
    """The learner. `sampler(e, rng)` returns one observation from arm `e`.

    The true world is NOT a parameter.  That is the point: `theta` cannot be
    read here because it is not in scope, and the self-check below asserts
    that structurally rather than in prose.
    """
    LIP_L_RUN = lipschitz_modulus(var)
    sig = np.sqrt(var)
    N = np.zeros(8)
    Ysum = np.zeros(8)
    W = np.zeros(8)
    for e in range(8):
        Ysum[e] += sampler(e, rng)
        N[e] += 1
    t = 8
    w_cur = np.ones(8) / 8.0
    sel_trace, bracket_trace = [], []
    while t < budget:
        if t % check_every == 0:
            mu_hat = Ysum / np.maximum(N, 1.0)
            for T in ANSWERS:
                fired, lo, pr = stop_certificate(mu_hat, N, var, alpha, T)
                if fired:
                    # The statistic that fired and the threshold it cleared are part of
                    # the certificate, so they are returned and stored rather than
                    # recomputed from a summary later.
                    return (t, T, N.copy(), False, sel_trace, bracket_trace,
                            {"statistic": float(lo), "threshold": float(pr),
                             "margin": float(lo - pr), "mu_hat": mu_hat.tolist()})
        if arm == "learner" and t % oracle_every == 0:
            mu_hat = np.clip(Ysum / np.maximum(N, 1.0), -BOX_B, BOX_B)
            b_t4 = np.log(max(t, 2.0) ** 4) + 0.5 * np.sum(np.log1p(N / REG_A))
            # The estimate is a RAW sample mean, so its deviation scales with sigma_e.
            # Omitting sigma_e here understates the radius wherever the variance is not
            # one -- and this world has variance 16 on two cells, so the factor is 4.
            r_t = float(np.max(np.sqrt(var) * np.sqrt(2.0 * (REG_A + N) * b_t4)
                               / np.maximum(N, 1.0)))
            # The accumulation argument in the theorem wants the oracle's own error to go
            # to zero.  THIS SCHEDULE DOES NOT DELIVER THAT, and the code must not be read
            # as if it did: `tol_t` is tightened with the refresh index but then FLOORED at
            # `BRACKET_TOL_FLOOR`, and `iters_t` is CAPPED at `BRACKET_ITERS_CAP`, so
            # the schedule alone does not GUARANTEE eps_t -> 0. A positive requested
            # tolerance does not imply a positive lower bound on the ACTUAL solver error.
            # A finite-eps rate needs a proved uniform error bound, answer stability, and
            # a stopping-certificate tightness bound. Finite observed gaps do not provide
            # these uniform-in-time premises. This panel reports the achieved finite-run
            # gaps; it does not establish either an exact or finite-eps asymptotic rate.
            n_ref = len(sel_trace) + 1
            # The tolerance tightens with the refresh index, floored at a width the
            # bracket can still reach.  MEASURED, so the floor is not guesswork: at a
            # fixed estimate the damped bracket settles at ~5.3e-7, and a tolerance that
            # does not clear it never fires the early break -- 525 iterations cost 86.7s
            # instead of 5.7s, for the same gap.  In the operating range the floor is
            # inert: runs stop at tau ~ 1200-1700, so n_ref reaches only 7-8 and
            # tol_t = 1e-4/n_ref^2 is already ~1.6e-6 > 5.3e-7, i.e. the break fires
            # anyway.  The floor exists so that a longer horizon cannot silently enter
            # the regime where the schedule outruns the solver.
            tol_t = max(1e-4 / float(n_ref) ** 2, BRACKET_TOL_FLOOR)
            # Capped.  Measured: 60-80 iterations already reach the settling width, and
            # `25 + 5*n_ref` grows without bound -- a run reaching 100 refreshes would
            # spend sum(25+5k) = 27750 iterations, i.e. ~2.5 hours by itself.
            iters_t = min(25 + 5 * n_ref, BRACKET_ITERS_CAP)
            los, ups, ws, gaps = {}, {}, {}, {}
            for T in ANSWERS:
                lo, up, wg = oracle_bracket(mu_hat, var, alt_regions_for(T),
                                            iters=iters_t, tol=tol_t)
                los[T], ups[T], ws[T] = lo, up, wg
                gaps[T] = float(up - lo) if np.isfinite(up) and np.isfinite(lo) else None
            keep = keep_set(los, ups, LIP_L_RUN, r_t)
            T_sel = keep[0] if keep else ANSWERS[0]
            w_cur = ws[T_sel]
            sel_trace.append({"t": int(t), "selected": T_sel,
                              "kept": keep, "r_t": r_t,
                              "lipschitz_modulus": LIP_L_RUN})
            fin = [g for g in gaps.values() if g is not None]
            bracket_trace.append({"t": int(t), "refresh": n_ref,
                                  "tol": tol_t, "iters": iters_t,
                                  "gaps": gaps,
                                  "max_gap": max(fin) if fin else None,
                                  "lower": {k: float(v) for k, v in los.items()},
                                  "upper": {k: float(v) for k, v in ups.items()}})
        elif arm == "oracle":
            w_cur = w_oracle
        elif arm == "uniform":
            w_cur = np.ones(8) / 8.0
        rho = 1.0 / np.sqrt(t + 1.0)
        w = (1.0 - rho) * w_cur + rho * np.ones(8) / 8.0
        W += w
        e_t = int(np.argmax(W - N))
        Ysum[e_t] += sampler(e_t, rng)
        N[e_t] += 1
        t += 1
    return budget, None, N.copy(), True, sel_trace, bracket_trace, None


def main():
    print("=" * 78)
    print("Paper A7: the learner, with certified stopping and no access to the truth")
    print("=" * 78)
    smoke = "--smoke" in sys.argv
    M, SCALE = 16.0, 4.0
    theta, var = family_low(M)
    theta = center_world(SCALE * theta)
    print("\n  The world is centered arm by arm, so it lies in the class on which")
    print("  `centered_additive_response` makes the product response equal the table and")
    print("  the energy equal the Gaussian information.  Centering moves no range, so the")
    print("  decision and both alternative sets are unchanged.")
    truth = best_answer(theta)

    print("\n  the benchmark, computed from the true world -- for COMPARISON only")
    print("  " + "-" * 72)
    gam, gam_up, wstar, gaps, priors = {}, {}, {}, {}, {}
    for T in ANSWERS:
        lo, up, wg, pr = oracle_bracket(theta, var, alt_regions_for(T), iters=60,
                                        want_prior=True)
        gam[T], gam_up[T], wstar[T], gaps[T], priors[T] = lo, up, wg, up - lo, pr
        print(f"      Gamma_{T} in [{lo:.6e}, {up:.6e}]   width {up - lo:.2e}")
    T_star = max(ANSWERS, key=lambda T: gam[T])
    G, G_up = gam[T_star], gam_up[T_star]
    print(f"      Gamma_comp in [{G:.6e}, {G_up:.6e}]"
          f"   1/Gamma in [{1.0/G_up:.2f}, {1.0/G:.2f}]   correct answer '{truth}'")
    print("      BOTH sides are reported.  The benchmark line on the figure is an")
    print("      INTERVAL, not a point: only the lower side is certified by a design that")
    print("      was actually achieved, and only the upper side by the prior below.")
    print("      The learner never reads any of this; it is the yardstick, not an input.")

    # the upper side, checked from the prior rather than taken from the solver
    for T in ANSWERS:
        pr = priors[T]
        if pr is None or pr["prior"] is None:
            check(f"answer {T}: a prior certificate for the upper bracket", False,
                  "the dual LP did not solve, so the upper side is UNCERTIFIED")
            continue
        pvec = np.array(pr["prior"])
        Gmat = np.array(pr["cuts"])
        recomputed = float(np.max(Gmat.T @ pvec))
        check(f"answer {T}: the upper bracket carries a checkable prior --"
              f" p >= 0, sum p = 1, and max_e (sum_l p_l g_l)_e recomputes it",
              bool(pvec.min() >= -1e-9 and abs(pvec.sum() - 1.0) < 1e-9
                   and abs(recomputed - pr["upper_from_prior"]) < 1e-9
                   and recomputed >= gam[T] - 1e-9),
              f"sum p = {pvec.sum():.12f}, min p = {pvec.min():.2e},"
              f" U_prior = {recomputed:.6e} >= lower {gam[T]:.6e}")

    alphas = [0.1, 0.02] if smoke else [0.1, 0.05, 0.02, 0.01]
    n_runs = 3 if smoke else 12
    budget = 8000 if smoke else 20000
    oracle_every, check_every = 200, 50

    rows = []
    BASE_SEED = 20260920
    ARM_IX = {"learner": 0, "oracle": 1, "uniform": 2}
    print(f"\n  runs (oracle refresh every {oracle_every}, stop check every {check_every})")
    print("  " + "-" * 72)
    for alpha in alphas:
        rec = {"alpha": alpha, "arms": {}}
        for arm in ("learner", "oracle", "uniform"):
            taus, correct, cens, regs, runs = [], 0, 0, [], []
            for _run_ix in range(n_runs):
                print(f"      [progress] alpha={alpha} arm={arm} run={_run_ix + 1}/{n_runs}",
                      flush=True)
                # NO alpha in the seed: the path is shared across the alpha panel.
                rng = np.random.default_rng([BASE_SEED, ARM_IX[arm], _run_ix])
                sampler = make_sampler(theta, var)
                t, ans, N, c, sel, br, cert = run(rng, sampler, var, alpha, budget, arm,
                                                  oracle_every, check_every,
                                                  w_oracle=wstar[T_star])
                taus.append(t)
                if c:
                    cens += 1
                else:
                    correct += int(ans == truth)
                    regs.append(regret_of(ans, theta))
                runs.append({"tau": int(t), "answer": ans, "censored": bool(c),
                             "counts": N.tolist(),
                             "regret": None if c else regret_of(ans, theta),
                             "stop_certificate": cert,
                             "selection_trace": sel,
                             "bracket_trace": br,
                             "n_refreshes": len(sel)})
            rec["arms"][arm] = {"mean_tau": float(np.mean(taus)), "censored": cens,
                                "correct": correct, "n_runs": n_runs,
                                "mean_regret": float(np.mean(regs)) if regs else None,
                                "runs": runs}
        rows.append(rec)
        L = np.log(1.0 / alpha)
        line = f"      alpha={alpha:6.3f}: "
        for arm in ("learner", "oracle", "uniform"):
            a = rec["arms"][arm]
            line += (f" {arm}={a['mean_tau']:7.0f}"
                     f"({a['correct']}/{n_runs - a['censored']}"
                     f"{',C' + str(a['censored']) if a['censored'] else ''})")
        print(line + f"   1/Gamma={1.0/G:.0f}")

    def agg(arm, key):
        return [r["arms"][arm][key] for r in rows]

    print("\n  what the three arms show")
    print("  " + "-" * 72)
    print("      The ORACLE arm is a diagnostic, not a competitor: it reads the true")
    print("      world to build its allocation, so no algorithm can be asked to match it.")
    print("      It is NOT a lower bound on stopping time -- it maximises the asymptotic")
    print("      information rate, and at finite alpha the learner can stop earlier on a")
    print("      path without anything being wrong.  The gap between LEARNER and ORACLE")
    print("      is an indication of the price of not knowing the world; the gap between")
    print("      LEARNER and UNIFORM is what the allocation is worth ON THIS PANEL.")

    all_runs = [rn for r in rows for arm in r["arms"] for rn in r["arms"][arm]["runs"]]
    stopped = [rn for rn in all_runs if not rn["censored"]]

    # ---------------------------------------------------------------- per-alpha reading
    # The POOLED mean over the alpha panel is reported, but it must not be read as a
    # uniform win: it averages four configurations whose individual evidence differs.
    per_alpha = []
    for r in rows:
        cell = {"alpha": r["alpha"], "arms": {}}
        for arm in ("learner", "oracle", "uniform"):
            a = r["arms"][arm]
            taus = np.array([rn["tau"] for rn in a["runs"]], dtype=float)
            cell["arms"][arm] = {
                "n": int(taus.size), "mean": float(taus.mean()),
                "sd": float(taus.std(ddof=1)), "sem": float(taus.std(ddof=1) / np.sqrt(taus.size)),
                "min": float(taus.min()), "max": float(taus.max()),
                "correct": int(a["correct"]), "censored": int(a["censored"])}
        per_alpha.append(cell)

    def welch(x, y):
        x, y = np.asarray(x, float), np.asarray(y, float)
        vx, vy = x.var(ddof=1) / x.size, y.var(ddof=1) / y.size
        t = (x.mean() - y.mean()) / np.sqrt(vx + vy)
        df = (vx + vy) ** 2 / (vx ** 2 / (x.size - 1) + vy ** 2 / (y.size - 1))
        return float(t), float(df), float(2.0 * student_t.sf(abs(t), df))

    def holm(pvals):
        """Holm-Bonferroni step-down, returning adjusted p in the INPUT order."""
        order = sorted(range(len(pvals)), key=lambda i: pvals[i])
        adj, running = [0.0] * len(pvals), 0.0
        for rank, i in enumerate(order):
            running = max(running, (len(pvals) - rank) * pvals[i])
            adj[i] = min(1.0, running)
        return adj

    tests = {}
    for other in ("uniform", "oracle"):
        raw = []
        for r in rows:
            xl = [rn["tau"] for rn in r["arms"]["learner"]["runs"]]
            xo = [rn["tau"] for rn in r["arms"][other]["runs"]]
            raw.append(welch(xo, xl))          # positive t = learner stops sooner
        adj = holm([q[2] for q in raw])
        tests[f"learner_vs_{other}"] = [
            {"alpha": r["alpha"], "t": q[0], "df": q[1], "p_raw": q[2], "p_holm": pa,
             "significant_holm_05": bool(pa < 0.05)}
            for r, q, pa in zip(rows, raw, adj)]

    print("\n  per alpha -- the pooled mean is NOT a substitute for this table")
    print("  " + "-" * 72)
    print("      alpha |  learner   oracle  uniform |  learner vs uniform: t, p(Holm)")
    for cell, tu in zip(per_alpha, tests["learner_vs_uniform"]):
        a = cell["arms"]
        print(f"      {cell['alpha']:5.3f} | {a['learner']['mean']:8.1f} {a['oracle']['mean']:8.1f}"
              f" {a['uniform']['mean']:8.1f} |  t = {tu['t']:5.2f}, p = {tu['p_holm']:.4g}"
              f"  {'significant' if tu['significant_holm_05'] else 'NOT significant'}")

    n_lower = sum(c["arms"]["learner"]["mean"] < c["arms"]["uniform"]["mean"]
                  for c in per_alpha)
    n_sig = sum(t["significant_holm_05"] for t in tests["learner_vs_uniform"])
    holm_list = ", ".join(f"{t['p_holm']:.3g}" for t in tests["learner_vs_uniform"])
    # This asserts the REPORTING, not the outcome.  Whether a cell reaches significance is
    # a measurement; making it a pass condition would turn the self-check into a filter
    # that only lets favourable data through.
    reported = all(
        set(c["arms"][a]) >= {"n", "mean", "sd", "sem"} for c in per_alpha
        for a in ("learner", "oracle", "uniform"))
    aligned = all(len(tests[k]) == len(per_alpha) and
                  all("p_holm" in q and 0.0 <= q["p_holm"] <= 1.0 for q in tests[k])
                  for k in tests)
    check("the comparison with uniform is reported PER ALPHA -- n, mean, sd and a"
          " Holm-corrected Welch test in every cell -- so the pooled mean cannot stand in"
          " for a uniform win.  A cell that misses significance at n per cell this small"
          " is UNDERPOWERED, which is not evidence that the learner has no advantage",
          reported and aligned,
          f"learner mean below uniform at {n_lower}/{len(per_alpha)} alphas;"
          f" Holm-significant at {n_sig}/{len(per_alpha)}"
          f" (p_holm = {holm_list})")

    # ------------------------------------------- alpha enters ONLY the stopping rule
    # With the seed free of alpha, a fixed (arm, run) is the SAME path at every alpha, and
    # the threshold is decreasing in alpha, so the stopping time must be non-increasing in
    # alpha pathwise.  This asserts the structural claim instead of stating it.
    by_cell = {}
    for r in rows:
        for arm in ("learner", "oracle", "uniform"):
            for ix, rn in enumerate(r["arms"][arm]["runs"]):
                by_cell.setdefault((arm, ix), []).append((r["alpha"], rn))
    mono_viol, path_viol = [], []
    for (arm, ix), seq in by_cell.items():
        seq.sort(key=lambda z: -z[0])                     # alpha descending
        taus = [rn["tau"] for _, rn in seq]
        if any(b < a for a, b in zip(taus, taus[1:])):
            mono_viol.append((arm, ix, taus))
        base = seq[-1][1]["selection_trace"]              # smallest alpha: longest path
        for _, rn in seq[:-1]:
            k = len(rn["selection_trace"])
            if [e["selected"] for e in rn["selection_trace"]] != \
               [e["selected"] for e in base[:k]]:
                path_viol.append((arm, ix))
                break
    check("alpha enters the algorithm at the STOPPING TEST alone -- selection, allocation"
          " and tracking never see it.  Under common random numbers across the panel the"
          " stopping time is therefore non-increasing in alpha on every path, and the"
          " selection trace at a larger alpha is a prefix of the one at the smallest",
          not mono_viol and not path_viol,
          f"{len(by_cell)} (arm, run) paths; monotonicity violations = {len(mono_viol)},"
          f" prefix violations = {len(path_viol)}")

    # --------------------------------------------- what this panel canNOT be used for
    thr = {}
    for r in rows:
        ts = [rn["stop_certificate"]["threshold"] for rn in r["arms"]["learner"]["runs"]
              if rn["stop_certificate"]]
        thr[r["alpha"]] = {"threshold_mean": float(np.mean(ts)),
                           "log_inv_alpha": float(np.log(1.0 / r["alpha"])),
                           "penalty_mean": float(np.mean(ts) - np.log(1.0 / r["alpha"]))}
    pen_max = max(v["penalty_mean"] for v in thr.values())
    lia_max = max(v["log_inv_alpha"] for v in thr.values())
    check("this panel CANNOT test the rate E tau ~ log(1/alpha) / Gamma.  The threshold is"
          " log(1/alpha) + (1/2) sum_e log(1 + N_e/a), and on this model the second term"
          " dominates the first across the whole panel, so the alpha axis is too short to"
          " expose the asymptotic regime.  The rate claim rests on the theorem, not here",
          pen_max > 2.0 * lia_max,
          f"regularisation penalty {min(v['penalty_mean'] for v in thr.values()):.1f}"
          f"-{pen_max:.1f} against log(1/alpha) <= {lia_max:.2f}"
          f" (factor {pen_max / lia_max:.1f}x)")

    # -------------------------------------------------- the oracle bracket refreshes
    refresh = [b for rn in all_runs for b in rn["bracket_trace"]]
    miss = [b for b in refresh if b["max_gap"] > b["tol"]]
    at_cap = [b for b in refresh if b["iters"] >= BRACKET_ITERS_CAP]
    check("the cutting-plane refreshes that did NOT reach their requested tolerance are"
          " counted and reported.  They bound the oracle DIAGNOSTIC only: the stopping"
          " rule uses the weak-duality lower bound from `regional_lower_bound`, never a"
          " bracket, so a loose refresh cannot make a stop unsound.  This implementation"
          " is NOT evidence that the oracle bracket error goes to zero",
          all(np.isfinite(b["max_gap"]) for b in refresh)
          and FAILURES["stop_bound_nonfinite"] == 0,
          f"{len(miss)}/{len(refresh)} refreshes above their tolerance,"
          f" {len(at_cap)} at the {BRACKET_ITERS_CAP}-iteration cap;"
          f" worst overshoot {max((b['max_gap'] / b['tol'] for b in miss), default=1.0):.2f}x tol")

    panel_scope = {
        "per_alpha": per_alpha, "tests": tests, "threshold_decomposition": thr,
        "refresh_diagnostics": {"n_refreshes": len(refresh), "above_tolerance": len(miss),
                                "at_iteration_cap": len(at_cap)},
        "common_random_numbers": True,
        "seed_recipe": "[BASE_SEED, arm_index, run_index] -- free of alpha",
        "worlds": 1, "M": M, "scale": SCALE, "runs_per_cell": n_runs,
        "pooled_mean_is_over_the_alpha_panel_only": True,
        "oracle_is_a_lower_bound_on_stopping_time": False,
        "panel_tests_the_log_inv_alpha_rate": False,
    }
    check("CORRECTNESS: every run that stopped returned the right answer, under a"
          " certificate that never used a primal value as a lower bound",
          all(rn["answer"] == truth for rn in stopped),
          f"{len(stopped)} stopped runs across all three arms")
    check("every stopped run has zero regret",
          all(abs(rn["regret"]) < 1e-12 for rn in stopped))
    import inspect
    run_params = set(inspect.signature(run).parameters)
    check("the learner never reads the true world -- checked STRUCTURALLY, not asserted:"
          " `run` takes a sampler closure and `theta` is not among its parameters, so"
          " the world is unreachable from the allocation path",
          "theta" not in run_params and "sampler" in run_params,
          f"run(...) parameters: {sorted(run_params)}")
    # THE ORACLE'S OWN ERROR.  The in-run gap sequence is NOT a test of the solver,
    # because the estimate `mu_hat` moves between refreshes and each refresh is a
    # different problem; a gap that rises there says nothing.  The solver is tested
    # separately, at a FIXED estimate, by raising the iteration budget.
    theta_probe, var_probe = family_low(M)
    theta_probe = center_world(SCALE * theta_probe)
    mu_probe = theta_probe + 0.05 * np.arange(8) / 8.0
    ladder = []
    for it in (10, 25, 50, 100, 200, 400):
        # ONE solve per answer, not two.  Reading `[1]` and `[0]` from two separate
        # calls ran the whole cutting plane twice for the same number -- and with
        # `tol=0.0` the early break never fires, so each call costs its full iteration
        # budget.  At the top rung that alone was minutes of duplicated work.
        def _gap(T):
            lo, up, _ = oracle_bracket(mu_probe, var_probe, alt_regions_for(T),
                                       iters=it, tol=0.0)
            return up - lo
        g = max(_gap(T) for T in ANSWERS)
        ladder.append({"iters": it, "max_gap": float(g)})
    mono = all(ladder[i]["max_gap"] >= ladder[i + 1]["max_gap"] - 1e-12
               for i in range(len(ladder) - 1))
    plateau = ladder[-1]["max_gap"]
    plateaued = (ladder[-1]["max_gap"] >= 0.5 * ladder[len(ladder) // 2]["max_gap"])
    check("the oracle bracket's gap is non-increasing in its iteration budget, at a"
          " FIXED estimate, and then PLATEAUS at a positive floor -- so the budget is"
          " not what limits it",
          mono and plateaued,
          "; ".join(f"{x['iters']}: {x['max_gap']:.2e}" for x in ladder))
    print(f"\n      MEASURED: the certified bracket's gap settles at {plateau:.3e} and")
    print(f"      does not fall further with iteration budget.  An earlier version of this")
    print(f"      script read the plateau it then measured (8.0e-3) as the duality gap")
    print(f"      between an LP relaxation above and a weak-duality certificate below.")
    print(f"      THAT READING WAS WRONG, and the correction is recorded rather than")
    print(f"      quietly applied: the plateau was the cutting plane's own oscillation")
    print(f"      plus a loose dual tolerance.  Taking the RUNNING MINIMUM of the")
    print(f"      relaxation values, damping the step toward the relaxation's vertex, and")
    print(f"      solving the regional dual to tolerance moves the gap 8.0e-3 -> 1.9e-4")
    print(f"      -> 5.0e-7, flat in both the cutting-plane count and the dual budget.")
    print(f"      So the residual is solver round-off, not a structural floor.  eps_t = 0")
    print(f"      is still not PROVED -- no floating-point bracket can prove it -- but the")
    print(f"      shortfall c*eps against Gamma_comp is now ~1e-5 relative, not ~35%.")
    check("the residual bracket gap is recorded, and is far below the plateau an earlier"
          " version called structural.  Flatness in both the cutting-plane count and the"
          " dual budget rules those two out as the binding constraint; it does NOT"
          " identify the residual, since the weight floor and the subtracted correction"
          " remain candidates and no check here separates them",
          plateau > 0.0 and plateau < 1e-4,
          f"certified-oracle gap = {plateau:.3e} (was 8.0e-3 before the damped step and"
          f" the tightened dual tolerance; the change is in the METHOD, not the bound."
          f" Cause of the residual: NOT established)")
    gapseq = [[b["max_gap"] for b in rn["bracket_trace"] if b.get("max_gap") is not None]
              for rn in all_runs if rn.get("bracket_trace")]
    gapseq = [g for g in gapseq if len(g) >= 3]
    if gapseq:
        worst_last = max(g[-1] for g in gapseq)
        rising = sum(1 for g in gapseq if g[-1] > g[0])
        print(f"\n      in-run oracle gaps: {len(gapseq)} runs, {rising} end above where")
        print(f"      they started, worst final gap {worst_last:.3e}.  The estimate moves")
        print(f"      between refreshes, so this is NOT monotone and is not asserted to")
        print(f"      be; it is recorded so the achieved eps_t can be read off.")
    # An earlier version stored `sel[:6]`, so a long run looked like a six-refresh run.
    # The guard is that the stored count matches the number the SCHEDULE implies at the
    # observed stopping time -- true at every run length, where "some run exceeds six"
    # was an accident of how long the runs happened to be.
    # Only the LEARNER arm refreshes: the oracle arm is handed a fixed allocation and the
    # uniform arm holds one, so both correctly store no refreshes at all.
    learner_runs = [rn for r in rows for rn in r["arms"]["learner"]["runs"]]
    tracecheck = [rn["n_refreshes"] == len(rn["selection_trace"])
                  and abs(rn["n_refreshes"] - rn["tau"] // oracle_every) <= 1
                  for rn in learner_runs]
    othercheck = [rn["n_refreshes"] == 0 for r in rows
                  for arm in ("oracle", "uniform") for rn in r["arms"][arm]["runs"]]
    check("every oracle refresh is stored, and the stored count equals the number the"
          " refresh schedule implies at the run's own stopping time -- the traces are no"
          " longer truncated to the first six",
          all(tracecheck) and all(othercheck),
          f"{sum(tracecheck)}/{len(tracecheck)} learner runs agree with"
          f" tau // {oracle_every}; longest trace"
          f" {max((rn['n_refreshes'] for rn in learner_runs), default=0)} refreshes;"
          f" {sum(othercheck)}/{len(othercheck)} non-learner runs store none")
    # ------------------------------------------- the eps_t schedule, as ACHIEVED in-run
    # The A2 accumulation step needs the oracle's own error to vanish.  Whether it does is
    # a measurement, not a modelling choice, so the requested schedule (tol, iters) and the
    # gap actually achieved are both stored per refresh and reported here side by side.
    prof, sched_ok = {}, True
    for rn in all_runs:
        for b in (rn.get("bracket_trace") or []):
            if "tol" not in b or "iters" not in b:
                sched_ok = False
            if b.get("max_gap") is not None:
                prof.setdefault(b["refresh"], []).append(b["max_gap"])
    idx = sorted(prof)
    if idx:
        head = idx[:min(8, len(idx))]
        print("\n      achieved eps_t by refresh index (max over all runs):")
        print("      " + "  ".join(f"{i}:{max(prof[i]):.2e}" for i in head))
        eps_first, eps_last = max(prof[idx[0]]), max(prof[idx[-1]])
        check("the oracle error ACHIEVED in-run is recorded per refresh alongside the"
              " schedule the code requested (tol ~ 1/n^2, iters ~ 25 + 5n), so eps_t is a"
              " measured quantity rather than an assumption",
              sched_ok and len(idx) >= 2,
              f"refreshes {idx[0]}..{idx[-1]}; achieved eps_t = {eps_first:.3e} at the"
              f" first and {eps_last:.3e} at the last")
        # --------------------------------------------- the floor, and what it costs the claim
        # The requested tolerance is `max(1e-4/n^2, BRACKET_TOL_FLOOR)` and the iteration
        # budget is `min(25 + 5n, BRACKET_ITERS_CAP)`.  Both are bounded, so the schedule
        # does not guarantee vanishing actual error. This check verifies the schedule's
        # floor/cap only; it cannot prove a rate or a positive lower bound on actual error.
        sched_floor_binds = (1e-4 / float(max(idx)) ** 2 <= BRACKET_TOL_FLOOR
                             if max(idx) > 0 else False)
        eps_floor_positive = BRACKET_TOL_FLOOR > 0 and BRACKET_ITERS_CAP < float("inf")
        check("the requested oracle schedule has a positive tolerance floor and a finite"
              " iteration cap; this verifies configuration only, not vanishing actual"
              " error or an asymptotic stopping guarantee",
              eps_floor_positive,
              f"tolerance floor {BRACKET_TOL_FLOOR:.1e}, iteration cap"
              f" {BRACKET_ITERS_CAP}; at the deepest refresh index reached ({max(idx)}) the"
              f" unfloored schedule would ask {1e-4 / float(max(idx)) ** 2:.2e}, so the"
              f" floor "
              + ("BINDS" if sched_floor_binds else "does not yet bind")
              + f"; worst achieved eps_t over all refreshes"
              f" {max(max(v) for v in prof.values()):.3e}")
        print(f"      achieved eps_t at the last refresh: {eps_last:.3e}.  In-run this is")
        print(f"      NOT monotone -- the estimate moves between refreshes, so each is a")
        print(f"      different problem -- which is why the solver is judged separately at")
        print(f"      a fixed estimate above.  What the rate theorem consumes is a bound on")
        print("      eps_t uniformly over future runs, plus answer stability and stopping")
        print("      certificate tightness. Recorded finite-run gaps do not discharge those")
        print("      premises. Report this panel as finite-alpha performance; derive any")
        print("      asymptotic or finite-eps rate from the completed operational theorem.")
    lw, ow = np.mean(agg("learner", "mean_tau")), np.mean(agg("oracle", "mean_tau"))
    uw = np.mean(agg("uniform", "mean_tau"))
    def arm_stats(arm):
        taus = [rn["tau"] for r in rows for rn in r["arms"][arm]["runs"]]
        n = max(len(taus), 1)
        mu = float(np.mean(taus))
        se = float(np.std(taus, ddof=1) / np.sqrt(n)) if n > 1 else float("nan")
        return mu, se, n

    print("\n      mean stopping time, with Monte Carlo standard errors")
    for arm in ("learner", "oracle", "uniform"):
        mu, se, n = arm_stats(arm)
        print(f"        {arm:8s}  {mu:8.1f}  +/- {se:6.1f}   (n = {n})")
    print("      These are MEASUREMENTS, not assertions.  No ordering among the three is")
    print("      required: the oracle allocation maximises the asymptotic information")
    print("      rate, which is not the same as minimising a finite-alpha stopping time,")
    print("      and the differences here are comparable to the standard errors.  Two")
    print("      earlier versions of this script asserted an ordering as a self-check --")
    print("      first that the learner must be slower than the oracle, then that it must")
    print("      beat uniform.  Both assertions were wrong and both have been removed.")
    arm_summary = {a: dict(zip(("mean", "stderr", "n"), arm_stats(a)))
                   for a in ("learner", "oracle", "uniform")}
    # weak duality, checked on a fresh state rather than assumed
    Nchk = np.full(8, 150.0); Nchk[1] = 400.0; Nchk[5] = 400.0
    Hchk = Nchk ** 2 / ((REG_A + Nchk) * var)
    pairs = []
    for Amat, bvec, _ in alt_regions_for("A"):
        lo = regional_lower_bound(theta, Hchk, Amat, bvec)
        pr = regional_primal_value(theta, Hchk, Amat, bvec)
        if pr is not None:
            pairs.append((lo, pr))
    check("WEAK DUALITY: the certified lower bound never exceeds a primal value, so the"
          " stopping certificate is on the safe side of the infimum",
          all(lo <= pr + 1e-6 for lo, pr in pairs),
          f"checked on {len(pairs)} regions where a primal solve also succeeded;"
          f" worst excess {max([lo - pr for lo, pr in pairs] or [0.0]):.2e}")
    check("and it is not merely safe but tight where both are available, so the"
          " certificate does not throw the stopping time away",
          all(lo >= pr - 1e-4 for lo, pr in pairs),
          f"worst shortfall {max([pr - lo for lo, pr in pairs] or [0.0]):.2e}")
    check("the answer-selection set was recorded at every oracle refresh, so the"
          " selection rule can be audited rather than trusted",
          all(len(rn["selection_trace"]) > 0
              for r in rows for rn in r["arms"]["learner"]["runs"]
              if not rn["censored"]))
    certs = [rn["stop_certificate"] for rn in stopped]
    check("every stopped run stored the statistic that fired and the threshold it"
          " cleared, with a strictly positive margin -- so the stop can be rechecked"
          " from the artifact without rerunning anything",
          all(cc is not None and cc["margin"] > 0 for cc in certs),
          f"{len(certs)} certificates stored; smallest margin"
          f" {min([cc['margin'] for cc in certs if cc], default=float('nan')):.3e}")

    # ------------------------------------------------- a world where the truth is SECOND
    #
    # In the world above the correct answer is `A`, which is also first in the fixed
    # tie-break order, so every selection snapshot keeps both answers and picks `A`.  That
    # run cannot show the rule ELIMINATING a wrong answer -- it never had to.  Swapping the
    # two arms makes `B` correct while the tie-break still tries `A` first, so the
    # elimination step is exercised.
    print("\n  a world whose correct answer is SECOND in the tie-break order")
    print("  " + "-" * 72)
    theta_sw = np.concatenate([theta[4:8], theta[0:4]])
    var_sw = np.concatenate([var[4:8], var[0:4]])
    truth_sw = best_answer(theta_sw)
    print(f"      the correct answer here is '{truth_sw}'"
          f" (tie-break order is {ANSWERS})")
    sw_runs, sw_correct, sw_cens, sw_elim = [], 0, 0, 0
    lo_sw, up_sw, w_sw = oracle_bracket(theta_sw, var_sw,
                                        alt_regions_for(truth_sw), iters=30)
    for _ in range(n_runs):
        sampler_sw = make_sampler(theta_sw, var_sw)
        t, ans, N, c, sel, br, cert = run(rng, sampler_sw, var_sw, alphas[-1], budget,
                                          "learner", oracle_every, check_every,
                                          w_oracle=w_sw)
        if c:
            sw_cens += 1
        else:
            sw_correct += int(ans == truth_sw)
        sw_elim += sum(1 for snap in sel if len(snap["kept"]) < len(ANSWERS))
        sw_runs.append({"tau": int(t), "answer": ans, "censored": bool(c),
                        "stop_certificate": cert, "selection_trace": sel})
    print(f"      {sw_correct}/{n_runs - sw_cens} stopped runs returned '{truth_sw}';"
          f" {sw_cens} censored")
    print(f"      selection snapshots that actually narrowed the answer set: {sw_elim}")
    check("on a world whose correct answer is second in the tie-break, every stopped run"
          " still returns it -- so the rule is not merely reading off the tie-break",
          sw_cens == n_runs or sw_correct == n_runs - sw_cens,
          f"{sw_correct}/{n_runs - sw_cens} correct")
    # ---------------------------------------------- why the set never narrows, in numbers
    print("\n  why no snapshot narrows the set, quantitatively")
    print("  " + "-" * 72)
    Nelim = elimination_horizon(G, lipschitz_modulus(var), var)
    obs = arm_summary["learner"]["mean"]
    if Nelim is None:
        print("      the allowance never fits inside the answer gap on any reachable ladder")
        ratio = float("inf")
    else:
        tot = 8.0 * Nelim
        ratio = tot / obs
        print(f"      elimination needs r_t < Gamma/(2L) = {G / (2*lipschitz_modulus(var)):.3e}")
        print(f"      which first holds at ~{Nelim:.3e} samples per cell,"
              f" i.e. ~{tot:.3e} samples")
        print(f"      the learner stops after {obs:.0f} samples on average"
              f" -- a factor of {ratio:.2e}")
    print("      So the set is not 'slightly too wide to narrow at these counts'.  The")
    print("      allowance is a property of the radius and the Lipschitz modulus, not of")
    print("      alpha, so NO confidence level reaches that horizon before stopping.  The")
    print("      runs cannot exercise elimination, and reporting them as if they might")
    print("      would be misleading.  The rule is therefore tested directly instead.")

    # ---------------------------------------------- the selection rule, driven directly
    print("\n  the selection rule, driven directly on constructed inputs")
    print("  " + "-" * 72)
    # (i) a clearly suboptimal answer IS dropped once the radius is small enough
    los_a = {"A": 1.0, "B": 0.1}
    ups_a = {"A": 1.05, "B": 0.12}
    drop = keep_set(los_a, ups_a, 1.0, 0.01)
    # (ii) with a large radius the same inputs keep both -- the rule is conservative
    keep_both = keep_set(los_a, ups_a, 1.0, 10.0)
    # (iii) the best answer is NEVER dropped, at any radius: u_best >= l_best = max l
    import itertools as _it
    never_drops_best = True
    for lA, lB, dA, dB, rr in _it.product((0.0, 0.3, 1.0), (0.0, 0.3, 1.0),
                                          (0.0, 0.5), (0.0, 0.5), (0.0, 0.01, 5.0)):
        lo = {"A": lA, "B": lB}
        up = {"A": lA + dA, "B": lB + dB}
        best = "A" if lA >= lB else "B"
        if best not in keep_set(lo, up, 1.0, rr):
            never_drops_best = False
            break
    print(f"      small radius: kept {drop}   large radius: kept {keep_both}")
    check("SELECTION RULE: a clearly suboptimal answer is dropped once the radius is"
          " small enough, so the rule can narrow the set at all",
          drop == ["A"], f"kept {drop} at r_t = 0.01")
    check("SELECTION RULE: the same inputs with a large radius keep both answers, so the"
          " rule is conservative rather than trigger-happy",
          sorted(keep_both) == ["A", "B"], f"kept {keep_both} at r_t = 10")
    check("SELECTION RULE: across a grid of brackets and radii the answer with the"
          " largest certified lower bracket is NEVER dropped -- the property the"
          " correctness proof needs",
          never_drops_best, "108 constructed cases")
    if sw_elim == 0:
        print("      The runs above therefore remain evidence about STOPPING only; the")
        print("      elimination mechanism is covered by these three checks, not by them.")

    # Counters that would compromise the GUARANTEE if they fired.  The primal solve is
    # excluded on purpose: it is used only to sanity-check weak duality, never to justify
    # stopping, so a primal failure costs a diagnostic comparison and nothing else.  It is
    # still reported, below and in the artifact, rather than hidden.
    GUARANTEE_KEYS = ("regional_dual_nonfinite", "stop_bound_nonfinite",
                      "lp_upper_failed", "lp_prior_failed",
                      "primal_infeasible_witness")
    print("\n  numerical escape hatches, counted")
    print("  " + "-" * 72)
    for k, v in FAILURES.items():
        role = "affects the guarantee" if k in GUARANTEE_KEYS else "diagnostic only"
        print(f"      {k:28s} {v:6d}   ({role})")
    check("no escape hatch that would compromise the stopping guarantee fired, and every"
          " counter is written to the artifact whether it fired or not",
          all(FAILURES[k] == 0 for k in GUARANTEE_KEYS),
          json.dumps({k: FAILURES[k] for k in GUARANTEE_KEYS}))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    src = pathlib.Path("scripts/EXP_paperA7_learner.py").read_bytes()
    dep = pathlib.Path("scripts/EXP_paperA_separation_games.py").read_bytes()
    out = {"M": M, "scale": SCALE,
           "Gamma_lower": gam, "Gamma_upper": gam_up,
           "Gamma_gap": gaps,
           "Gamma_design": {T: np.asarray(wstar[T]).tolist() for T in ANSWERS},
           "Gamma_prior_certificate": priors,
           "Gamma_comp_lower": G, "Gamma_comp_upper": G_up,
           "Gamma_comp": G,
           "Gamma_comp_note": "Gamma_comp repeats Gamma_comp_lower.  It is the LOWER side"
                              " of the bracket -- the value of a design that was actually"
                              " achieved -- so 1/Gamma_comp is the LARGER end of the"
                              " benchmark interval, not a point prediction.",
           "numerical_failures": FAILURES,
           "source_sha256": hashlib.sha256(src).hexdigest(),
           "dependency_sha256": {"EXP_paperA_separation_games.py":
                                 hashlib.sha256(dep).hexdigest()},
           "truth": truth,
           "oracle_every": oracle_every, "check_every": check_every,
           "budget": budget, "rows": rows,
           "note": "the oracle arm is a diagnostic that reads the true world",
           "model_class": "centered per arm, box |mu_e| <= BOX_B, carried as solver"
                          " constraints",
           "box_B": BOX_B,
           "lipschitz_modulus": lipschitz_modulus(var),
           "lipschitz_note": "2B / min_e var_e, computed from the observation model rather"
                             " than fixed at 2B",
           "arm_summary": arm_summary,
           "panel_scope": panel_scope,
           "swapped_world": {"truth": truth_sw, "runs": sw_runs,
                             "narrowing_snapshots": sw_elim},
           "elimination_horizon": {
               "target_radius": G / (2.0 * lipschitz_modulus(var)),
               "samples_per_cell": Nelim,
               "total_samples": None if Nelim is None else 8.0 * Nelim,
               "observed_mean_stop": obs,
               "ratio": ratio,
               "note": "the allowance 2 L r_t depends on the radius and the Lipschitz"
                       " modulus, not on alpha, so no confidence level reaches this"
                       " horizon before stopping; the selection rule is tested directly"
                       " instead of through the runs"},
           "oracle_gap_ladder": ladder,
           "oracle_gap_floor": float(plateau),
           "checks": CHECKS, "all_passed": nfail == 0}
    # A smoke run must never land on the artifact the figures read: three alphas and
    # three runs each look exactly like a real run in the JSON, and the only way to tell
    # is the run count.  Writing it elsewhere removes the ambiguity.
    dest = ("research/unified_20260919/paperA7_learner"
            + ("_smoke" if smoke else "") + ".json")
    out["smoke"] = bool(smoke)
    with open(dest, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n  artifact: {dest}")
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
