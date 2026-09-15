"""Semantic deduplication of mined candidate relations.

``mine.discover_inequalities`` already applies three syntactic filters
(variation, non-identity, tight-somewhere-and-slack-somewhere) plus an
exact-rational affine-alias exclusion.  Those filters are necessary but not
sufficient: the same physical quantity is emitted under several
(equation, symbol) names across the portfolio (e.g. the radius r_Omega(S) is
recorded as ``SUP.exact_radius.radius``, ``SUP.modular_formula.radius_exact``,
``SUP.component_perturbation.r_hat``/``r_true`` and
``STR.budget_optima.opt_value``), and several equations *declare* an
inequality whose two sides then get rediscovered as a "new" relation, or
declare a slack/ratio symbol whose numerator, denominator or defining
difference gets rediscovered the same way.  None of that is a scientific
finding; all of it is noise that drowns the real candidates.

This module re-examines each candidate produced by
``discover_inequalities`` against the *raw row store* (not the collapsed
min/max fact table mine.py mines from) and classifies it into exactly one of
five tiers:

* ``TAUTOLOGY``   -- derivable from the registry's own declarations: the two
  sides are the ``lhs``/``rhs`` of the same declared equation, one side is
  that equation's own ``ratio`` versus its numerator or denominator, or the
  difference of the two sides is (up to a verified exact affine transform)
  an already-declared ``slack`` symbol of that same equation.
* ``ALIAS``       -- the two series are numerically identical, or related by
  a verified exact affine map, on every jointly measured instance.  Nothing
  here is a discovery; it is the same number (or a monotone rescaling of it)
  wearing two names.
* ``DEGENERATE``  -- the joint support is too small, near-constant, one side
  is identically zero, or every jointly measured row comes from a single
  world family.
* ``REPARAM``     -- neither an alias nor degenerate, but the two series are
  perfectly rank-correlated (Spearman rho ~ +-1) on the observed range: very
  likely one is a monotone reparametrization of the other.  Flagged, not
  dropped -- confidence is lower than a genuine inequality between two
  independently varying quantities, but this is evidence, not proof, of
  reparametrization.
* ``NOVEL_CANDIDATE`` -- survives every check above.  This is what the
  discovery pass exists to find.

Nothing is deleted.  Every input candidate keeps its original fields and
gains a ``tier``, a ``reason`` string, a ``verified_support`` (the joint
support recomputed on the *full* instance key rather than mine.py's
(world_id, k) join), an ``n_families`` count (how many distinct
``instance["family"]`` values the joint support spans -- a relation seen on
one family is much weaker evidence than one seen on five) and, for
NOVEL_CANDIDATE rows, a handful of concrete tight instances.

Everything here is heuristic evidence over the store's own numbers, not a
theorem prover: an ALIAS/TAUTOLOGY verdict is verified exactly wherever the
underlying rows are exact rationals, and only degrades to a numeric
tolerance check when rows are float-mode.  See the module docstring's
"false positive / false negative risk" note in mine.py's CLI help and the
accompanying report for what that means in practice.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

TIER_TAUTOLOGY = "TAUTOLOGY"
TIER_ALIAS = "ALIAS"
TIER_DEGENERATE = "DEGENERATE"
TIER_REPARAM = "REPARAM"
TIER_NOVEL = "NOVEL_CANDIDATE"

TIERS = (TIER_TAUTOLOGY, TIER_ALIAS, TIER_DEGENERATE, TIER_REPARAM, TIER_NOVEL)

# Below this many jointly-measured rows a verdict either way is not worth
# trusting; the candidate is parked in DEGENERATE with an explicit reason
# rather than silently promoted to NOVEL_CANDIDATE for lack of evidence.
MIN_JOINT_SUPPORT = 5

# Spearman |rho| at or above this, on a relation that is not already an
# alias or a tautology, is treated as "very likely a monotone
# reparametrization" rather than two independently varying quantities.
REPARAM_RHO = 0.999


# ------------------------------------------------------------------ helpers

def _num(row: Mapping) -> Any:
    """Prefer the exact rational; fall back to the float; None when absent.

    Duplicated from ``mine._num`` deliberately: this module must not import
    mine.py (mine.py imports this module), and the coding rule is small
    enough that a shared helper module would be more indirection than the
    four lines it saves.
    """
    ex = row.get("exact")
    if ex:
        try:
            return Fraction(ex)
        except Exception:
            pass
    v = row.get("value")
    if v is None or isinstance(v, str):
        return None
    return v


def _base(col: str) -> str:
    """Strip the ``|min`` / ``|max`` suffix mine.py's fact-table columns carry."""
    if col.endswith("|min") or col.endswith("|max"):
        return col.rsplit("|", 1)[0]
    return col


def _split(col: str) -> Tuple[str, str]:
    """``'EQ_ID.symbol'`` -> ``(eq_id, symbol)``.  eq_id itself may contain dots."""
    eq_id, symbol = col.rsplit(".", 1)
    return eq_id, symbol


def _inst_key(r) -> Tuple:
    inst = r.get("instance") or {}
    return tuple(sorted((str(k), str(v)) for k, v in inst.items()))


def build_row_index(rows: Sequence[Mapping]):
    """``(eq_id, symbol) -> {inst_key: (value, family)}`` for measured rows.

    This joins on the *full* instance key, which is a finer granularity than
    the ``(world_id, k)`` join ``discover_inequalities`` uses for its fact
    table -- deliberately: alias/tautology verification should not be fooled
    by two distinct instances that happen to collide on ``world_id`` and
    ``k`` alone (a collision the original fact table already tracks and
    reports separately as ``join_key_collisions``).

    Also returns ``role_of``: ``(eq_id, symbol) -> role`` taken straight from
    the data (the row's own ``role`` field), so definitional-derivability
    checks use what the registry/emitter actually declared rather than
    re-guessing it from the symbol's name.
    """
    idx: Dict[Tuple[str, str], Dict[Tuple, Tuple[Any, str]]] = defaultdict(dict)
    role_of: Dict[Tuple[str, str], str] = {}
    for r in rows:
        if r.get("status") != "measured":
            continue
        v = _num(r)
        if v is None:
            continue
        key = (r["eq_id"], r["symbol"])
        role_of.setdefault(key, r.get("role"))
        ikey = _inst_key(r)
        col = idx[key]
        if ikey not in col:
            inst = r.get("instance") or {}
            col[ikey] = (v, str(inst.get("family", "unknown")))
    return idx, role_of


def _shared(idx, keyA, keyB):
    """Joint rows for two (eq_id, symbol) keys: list of (inst_key, x, y, family)."""
    da = idx.get(keyA, {})
    db = idx.get(keyB, {})
    if not da or not db:
        return []
    out = []
    for k in (da.keys() & db.keys()):
        x, famx = da[k]
        y, famy = db[k]
        fam = famx if famx != "unknown" else famy
        out.append((k, x, y, fam))
    return out


def build_coarse_index(rows: Sequence[Mapping]):
    """(eq_id, symbol) -> {(world_id, k): {'min':v,'max':v,'family':fam}}.

    This is the SAME join granularity ``discover_inequalities()``'s own fact
    table uses -- deliberately, as a fallback.  The full-instance-key join in
    ``build_row_index`` is the precise, preferred one, but it can come up
    empty for a genuinely cross-chain pair whose two probes stamp different
    *extra* instance fields for what is otherwise the same (world_id, k) --
    observed in practice between STRUCTURAL and SUPPORT chain rows.  Without
    this fallback that shape mismatch would silently demote a
    well-supported candidate to DEGENERATE for a reason that has nothing to
    do with whether the relation is real.
    """
    coarse: Dict[Tuple[str, str], Dict[Tuple[str, str], Dict[str, Any]]] = defaultdict(dict)
    for r in rows:
        if r.get("status") != "measured":
            continue
        v = _num(r)
        if v is None:
            continue
        inst = r.get("instance") or {}
        wid = inst.get("world_id")
        if wid is None:
            continue
        key = (r["eq_id"], r["symbol"])
        jkey = (str(wid), str(inst.get("k", "")))
        fam = str(inst.get("family", "unknown"))
        cell = coarse[key].get(jkey)
        if cell is None:
            coarse[key][jkey] = {"min": v, "max": v, "family": fam}
        else:
            if v < cell["min"]:
                cell["min"] = v
            if v > cell["max"]:
                cell["max"] = v
            if cell["family"] == "unknown" and fam != "unknown":
                cell["family"] = fam
    return coarse


def _shared_coarse(coarse, colA: str, colB: str):
    """Fallback join at (world_id, k) granularity, honoring each candidate
    column's own |max / |min statistic -- this reproduces exactly what
    ``discover_inequalities()`` itself compared to produce the candidate."""
    keyA, keyB = _split(_base(colA)), _split(_base(colB))
    statA = "max" if colA.endswith("|max") else "min"
    statB = "max" if colB.endswith("|max") else "min"
    da = coarse.get(keyA, {})
    db = coarse.get(keyB, {})
    if not da or not db:
        return []
    out = []
    for jkey in (da.keys() & db.keys()):
        x = da[jkey][statA]
        y = db[jkey][statB]
        fam = da[jkey]["family"] if da[jkey]["family"] != "unknown" else db[jkey]["family"]
        out.append((jkey, x, y, fam))
    return out


def _all_equal(pairs, *, tol: float = 1e-9) -> bool:
    """``x == y`` on every pair -- exact when both sides are Fraction."""
    if all(isinstance(x, Fraction) and isinstance(y, Fraction) for x, y in pairs):
        return all(x == y for x, y in pairs)
    scale = max(1.0, max(abs(float(y)) for _, y in pairs))
    return all(abs(float(x) - float(y)) <= tol * scale + tol for x, y in pairs)


def _fit_affine_verified(pairs, *, tol: float = 1e-9):
    """``y = alpha*x + beta`` fitted on two distinct x's, verified on all pairs.

    Returns ``(alpha, beta, exact)`` or ``None``.  ``exact`` is True only when
    every value involved was an exact ``Fraction`` and the fit is verified by
    exact rational equality; otherwise the fit is numeric and verified only
    to within ``tol`` (relative to the scale of the y series) -- callers that
    care about the PROVED/COMPILED/NUMERICAL distinction must treat a
    non-exact affine alias as numerical evidence, never as proof.
    """
    if len(pairs) < 3:
        return None
    if all(isinstance(x, Fraction) and isinstance(y, Fraction) for x, y in pairs):
        distinct = []
        for x, y in pairs:
            if all(x != x0 for x0, _ in distinct):
                distinct.append((x, y))
            if len(distinct) >= 2:
                break
        if len(distinct) < 2:
            return None
        (x0, y0), (x1, y1) = distinct
        if x1 == x0:
            return None
        alpha = (y1 - y0) / (x1 - x0)
        beta = y0 - alpha * x0
        if all(y == alpha * x + beta for x, y in pairs):
            return alpha, beta, True
        return None
    # Numeric fallback: pick the widest-separated x pair for stability.
    fx = [float(x) for x, _ in pairs]
    fy = [float(y) for _, y in pairs]
    x0 = fx[0]
    i1 = max(range(len(fx)), key=lambda i: abs(fx[i] - x0))
    x1, y1 = fx[i1], fy[i1]
    if abs(x1 - x0) < 1e-12:
        return None
    y0 = fy[0]
    alpha = (y1 - y0) / (x1 - x0)
    beta = y0 - alpha * x0
    scale = max(1.0, max(abs(v) for v in fy))
    for x, y in zip(fx, fy):
        if abs(y - (alpha * x + beta)) > tol * scale + tol:
            return None
    return alpha, beta, False


def _spearman(pairs) -> Optional[float]:
    """Spearman rank correlation (average-rank ties), or None if degenerate."""
    xs = [float(x) for x, _ in pairs]
    ys = [float(y) for _, y in pairs]
    n = len(xs)
    if n < 3:
        return None

    def ranks(vals):
        order = sorted(range(len(vals)), key=lambda i: vals[i])
        r = [0.0] * len(vals)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and vals[order[j + 1]] == vals[order[i]]:
                j += 1
            avg = (i + j) / 2.0 + 1.0
            for t in range(i, j + 1):
                r[order[t]] = avg
            i = j + 1
        return r

    rx, ry = ranks(xs), ranks(ys)
    mx, my = sum(rx) / n, sum(ry) / n
    sxx = sum((a - mx) ** 2 for a in rx)
    syy = sum((a - my) ** 2 for a in ry)
    if sxx <= 0 or syy <= 0:
        return None
    sxy = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    return sxy / (sxx * syy) ** 0.5


def _degenerate_reasons(pairs_full, *, min_distinct: int = 3) -> List[str]:
    """pairs_full: list of (inst_key, x, y, family)."""
    xs, ys, fams = set(), set(), set()
    zero_x, zero_y = True, True
    for _, x, y, fam in pairs_full:
        xs.add(x); ys.add(y); fams.add(fam)
        if x != 0:
            zero_x = False
        if y != 0:
            zero_y = False
    reasons = []
    if len(fams) <= 1:
        reasons.append("single_world_family(%s)" % (next(iter(fams), "?"),))
    if len(xs) < min_distinct or len(ys) < min_distinct:
        reasons.append("near_constant(distinct_lhs=%d,distinct_rhs=%d)" % (len(xs), len(ys)))
    if zero_x:
        reasons.append("lhs_identically_zero")
    if zero_y:
        reasons.append("rhs_identically_zero")
    return reasons


# --------------------------------------------------------- per-candidate

def classify_candidate(cand: Mapping, idx, role_of, *,
                        coarse=None,
                        min_support: int = MIN_JOINT_SUPPORT,
                        reparam_rho: float = REPARAM_RHO) -> Dict[str, Any]:
    """Classify one ``discover_inequalities`` candidate into a tier.

    Checks run in this order, each returning as soon as it fires:

    0. join selection: the precise full-instance-key join if it clears
       ``min_support``; otherwise, if ``coarse`` (from ``build_coarse_index``)
       is given, fall back to the (world_id, k) join ``discover_inequalities``
       itself used -- a cross-chain pair whose two probes stamp different
       extra instance fields can have zero overlap on the fine join despite
       ample coarse-join support, and that is a join-granularity artefact,
       not evidence the relation is degenerate.  ``out["join"]`` records
       which one was used.
    1. insufficient joint support on whichever join was used (parked as
       DEGENERATE, not guessed at)
    2. exact alias
    3. affine alias
    4. definitional derivability (same equation only): declared lhs<=rhs,
       ratio vs. its own numerator/denominator, or the difference equalling
       a declared slack symbol of the same equation
    5. degenerate (single family / near-constant / a side identically zero)
    6. monotone reparametrization (Spearman rho ~ +-1)
    7. otherwise: NOVEL_CANDIDATE
    """
    colA, colB = cand["lhs"], cand["rhs"]
    baseA, baseB = _base(colA), _base(colB)
    eqA, symA = _split(baseA)
    eqB, symB = _split(baseB)
    keyA, keyB = (eqA, symA), (eqB, symB)

    shared = _shared(idx, keyA, keyB)
    join_used = "full"
    if len(shared) < min_support and coarse is not None:
        cshared = _shared_coarse(coarse, colA, colB)
        if len(cshared) >= min_support:
            shared = cshared
            join_used = "coarse"

    out = dict(cand)
    out["lhs_base"] = baseA
    out["rhs_base"] = baseB
    out["verified_support"] = len(shared)
    out["join"] = join_used

    if len(shared) < min_support:
        out["tier"] = TIER_DEGENERATE
        out["reason"] = "insufficient_joint_support(n=%d,join=%s)" % (len(shared), join_used)
        out["n_families"] = len({fam for _, _, _, fam in shared})
        out["families"] = sorted({fam for _, _, _, fam in shared})
        return out

    families = sorted({fam for _, _, _, fam in shared})
    out["n_families"] = len(families)
    out["families"] = families
    xy = [(x, y) for _, x, y, _ in shared]

    if _all_equal(xy):
        out["tier"] = TIER_ALIAS
        out["reason"] = "exact_alias"
        return out

    fit = _fit_affine_verified(xy)
    if fit is not None:
        alpha, beta, exact = fit
        out["tier"] = TIER_ALIAS
        out["reason"] = "affine_alias(alpha=%s,beta=%s,exact=%s)" % (alpha, beta, exact)
        out["affine_alpha"] = str(alpha)
        out["affine_beta"] = str(beta)
        out["affine_exact"] = exact
        return out

    if eqA == eqB:
        roleA, roleB = role_of.get(keyA), role_of.get(keyB)
        if roleA == "lhs" and roleB == "rhs":
            out["tier"] = TIER_TAUTOLOGY
            out["reason"] = "declared_lhs_le_rhs(%s)" % eqA
            return out
        if roleA == "ratio" and roleB in ("lhs", "rhs"):
            out["tier"] = TIER_TAUTOLOGY
            out["reason"] = "ratio_vs_own_%s(%s)" % (roleB, eqA)
            return out
        if roleB == "ratio" and roleA in ("lhs", "rhs"):
            out["tier"] = TIER_TAUTOLOGY
            out["reason"] = "ratio_vs_own_%s(%s)" % (roleA, eqA)
            return out

        shared_by_key = {k: (x, y) for k, x, y, _ in shared}
        for (eqS, symS), role in role_of.items():
            if eqS != eqA or role != "slack" or (eqS, symS) in (keyA, keyB):
                continue
            sdict = idx.get((eqS, symS), {})
            triple = []
            for k, (x, y) in shared_by_key.items():
                if k in sdict:
                    sval, _ = sdict[k]
                    triple.append((y - x, sval))
            if len(triple) < min_support:
                continue
            if _all_equal(triple):
                out["tier"] = TIER_TAUTOLOGY
                out["reason"] = "diff_equals_slack(%s.%s)" % (eqS, symS)
                return out
            fit2 = _fit_affine_verified(triple)
            if fit2 is not None:
                a2, b2, ex2 = fit2
                out["tier"] = TIER_TAUTOLOGY
                out["reason"] = ("diff_affine_of_slack(%s.%s,alpha=%s,beta=%s,exact=%s)"
                                 % (eqS, symS, a2, b2, ex2))
                return out

    deg = _degenerate_reasons(shared)
    if deg:
        out["tier"] = TIER_DEGENERATE
        out["reason"] = ",".join(deg)
        return out

    rho = _spearman(xy)
    if rho is not None and abs(rho) >= reparam_rho:
        out["tier"] = TIER_REPARAM
        out["reason"] = "monotone_reparam(spearman=%.5f)" % rho
        out["spearman"] = rho
        return out

    def _inst_of(k):
        # full-join keys are tuples of (field, value) pairs -- dict(k) works
        # directly; coarse-join keys are a bare (world_id, k) pair of strings
        # and need to be labelled explicitly instead.
        if join_used == "full":
            return dict(k)
        return {"world_id": k[0], "k": k[1]}

    tight_examples = []
    for k, x, y, fam in shared:
        if x == y:
            tight_examples.append({"instance": _inst_of(k), "family": fam})
        if len(tight_examples) >= 5:
            break
    out["tier"] = TIER_NOVEL
    out["reason"] = "survives_alias_tautology_degenerate_reparam_checks"
    out["tight_examples"] = tight_examples
    if rho is not None:
        out["spearman"] = rho
    return out


# -------------------------------------------------------------- batch API

def classify_all(rows: Sequence[Mapping], candidates: Sequence[Mapping], *,
                  min_support: int = MIN_JOINT_SUPPORT,
                  reparam_rho: float = REPARAM_RHO,
                  use_coarse_fallback: bool = True) -> List[Dict[str, Any]]:
    """Classify every ``discover_inequalities`` candidate against ``rows``.

    ``use_coarse_fallback=True`` (the default) builds the (world_id, k)
    fallback index once and reuses it for every candidate -- see
    ``build_coarse_index`` / the join-selection note on ``classify_candidate``
    for why this matters for cross-chain candidates.  Pass False to force the
    strict full-instance-key join only (useful for diagnosing exactly how
    much of DEGENERATE is join-granularity artefact vs. genuine).
    """
    idx, role_of = build_row_index(rows)
    coarse = build_coarse_index(rows) if use_coarse_fallback else None
    return [classify_candidate(c, idx, role_of, coarse=coarse,
                                min_support=min_support, reparam_rho=reparam_rho)
            for c in candidates]


def tier_counts(classified: Sequence[Mapping]) -> Dict[str, int]:
    counts = {t: 0 for t in TIERS}
    for c in classified:
        counts[c["tier"]] = counts.get(c["tier"], 0) + 1
    return counts


def novel_candidates(classified: Sequence[Mapping]) -> List[Dict[str, Any]]:
    novel = [c for c in classified if c["tier"] == TIER_NOVEL]
    novel.sort(key=lambda c: (-(c["support"] * min(c["tight_rate"], 0.5)), -c["support"]))
    return novel


def alias_classes(classified: Sequence[Mapping]):
    """Union-find the ALIAS-tier pairs into equivalence classes for reporting.

    Returns ``(classes, edges)``: ``classes`` is a list of
    ``{"canonical": ..., "members": [...]}`` (canonical = lexicographically
    first member -- an arbitrary but stable choice; nothing scientific rides
    on which member is "canonical"), ``edges`` is the raw list of
    ``(a, b, reason)`` pairwise alias findings that produced them, so a
    reviewer can see exactly what got merged and why rather than trusting the
    union-find silently.
    """
    parent: Dict[str, str] = {}

    def find(x):
        parent.setdefault(x, x)
        root = x
        while parent[root] != root:
            root = parent[root]
        while parent[x] != root:
            parent[x], x = root, parent[x]
        return root

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    edges = []
    for c in classified:
        if c["tier"] == TIER_ALIAS:
            a, b = c["lhs_base"], c["rhs_base"]
            union(a, b)
            edges.append({"a": a, "b": b, "reason": c["reason"]})

    groups: Dict[str, set] = defaultdict(set)
    for node in list(parent):
        groups[find(node)].add(node)
    classes = []
    for members in groups.values():
        if len(members) > 1:
            ms = sorted(members)
            classes.append({"canonical": ms[0], "members": ms})
    classes.sort(key=lambda c: -len(c["members"]))
    return classes, edges
