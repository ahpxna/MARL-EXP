#!/usr/bin/env python3
"""D6, high-risk R3 (and direction 5): is choosing a good ALLOCATION cheaper, by an
order, than RECOVERING the whole label?

    C_allocation(q, eps, delta)  =  o( C_recover_A(q, delta) )  ?

The supervisor's conditions, all of which are respected below:
  * both sides use the SAME query library and the SAME cost;
  * the learner does NOT know the equivalence class in advance;
  * the loss from choosing wrongly is accounted for;
  * "do not force the result if every good-enough allocation actually pins down
     almost all of A -- a reduction in the reverse direction is a valuable negative
     result".

TWO PARTS.

PART 1, THE CORPUS'S OWN MODEL. Worlds are the hidden sets A of the compensated D6
world; a query is one physical coordinate read; an allocation is a retained set S
under a cardinality budget; S is eps-good at A when L_A(S) <= min_S' L_A(S') + eps.
  C_recover    = least worst-case depth of a tree that identifies A exactly.
  C_allocation = least worst-case depth after which ONE retained set is eps-good for
                 every world still consistent.
If C_allocation is 0 the separation is real but DEGENERATE -- one allocation was
already good everywhere and nothing had to be learned. That is reported as such, not
dressed up as a separation.

PART 2, A FAMILY BUILT TO SEPARATE NON-DEGENERATELY, plus its control:
  split(n)   : the eps-good allocation is decided by ONE bit while identifying the
               world needs all n -- so C_allocation = 1, C_recover = n.
  pinning(n) : every eps-good allocation determines the world, so the two costs
               coincide. This is the reverse reduction, and it is run to show the
               separation is a property of the instance and not of the definitions.

WHAT THIS DOES NOT ESTABLISH
 - Query DEPTH, zero error, deterministic trees. This is not a delta-PAC sample
   complexity: no confidence parameter appears anywhere, so nothing here is a
   statement about C(q, eps, delta) as written.
 - Exact on the listed sizes only.
 - Part 2 exhibits a family with a gap; it does not show the gap arises in the D6
   construction, and Part 1 says it does not, for the reason Part 1 gives.

    .venv/bin/python scripts/R3_allocation_vs_recovery.py
"""
from __future__ import annotations

from fractions import Fraction as Fr
from functools import lru_cache
import importlib.util, itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "g4", REPO / "scripts/G4_fixed_world_observation_classes.py")
g4 = importlib.util.module_from_spec(spec); spec.loader.exec_module(g4)


def depth_to(worlds, tests, done):
    """least worst-case depth of a tree whose every leaf satisfies `done`."""
    @lru_cache(maxsize=None)
    def d(C):
        if done(C):
            return 0
        best = None
        for e in range(len(tests)):
            yes = frozenset(h for h in C if tests[e][h])
            no = frozenset(h for h in C if not tests[e][h])
            if not yes or not no:
                continue
            v = 1 + max(d(yes), d(no))
            if best is None or v < best:
                best = v
        return best if best is not None else 10 ** 6
    return d(frozenset(worlds))


# --------------------------------------------------------------- part 1
def part1(k, t0, rho, eps):
    cfg = g4.make_cfg(k, t0, rho)
    Ws = g4.worlds(cfg)
    T = sorted(cfg["T"])
    L = {}
    for A in Ws:
        F = g4.world_fn(cfg, A)
        Q = {i: g4.response_levels(cfg, F, i) for i in range(cfg["m"])}
        for q in range(len(T) + 1):
            for S in itertools.combinations(T, q):
                L[(A, S)] = g4.compression_loss(cfg, F, Q, frozenset(S))
    Ds = [S for q in range(len(T) + 1) for S in itertools.combinations(T, q)]
    own = {A: min(L[(A, S)] for S in Ds) for A in Ws}
    good = {(A, S): (L[(A, S)] <= own[A] + eps) for A in Ws for S in Ds}
    # queries: read one coordinate of the hidden set, i.e. "is i in A?"
    tests = [{A: (i in A) for A in Ws} for i in range(cfg["m"]) if i != cfg["j"]]
    c_rec = depth_to(Ws, tests, lambda C: len(C) <= 1)
    c_alloc = depth_to(Ws, tests,
                       lambda C: any(all(good[(A, S)] for A in C) for S in Ds))
    return cfg, len(Ws), c_rec, c_alloc, Ds, own


# --------------------------------------------------------------- part 2
def split_family(n):
    """allocation decided by bit 0; identity needs every bit."""
    Ws = list(itertools.product((0, 1), repeat=n))
    Ds = ["S0", "S1"]
    loss = {(w, "S0"): Fr(0) if w[0] == 0 else Fr(1) for w in Ws}
    loss.update({(w, "S1"): Fr(0) if w[0] == 1 else Fr(1) for w in Ws})
    tests = [{w: bool(w[i]) for w in Ws} for i in range(n)]
    return f"split(n={n})", Ws, Ds, loss, tests


def pinning_family(n):
    """a distinct allocation per world: being eps-good pins the world down."""
    Ws = list(itertools.product((0, 1), repeat=n))
    Ds = [f"S{i}" for i in range(len(Ws))]
    loss = {(w, f"S{i}"): (Fr(0) if Ws[i] == w else Fr(1))
            for w in Ws for i in range(len(Ws))}
    tests = [{w: bool(w[i]) for w in Ws} for i in range(n)]
    return f"pinning(n={n})", Ws, Ds, loss, tests


def costs(Ws, Ds, loss, tests, eps):
    own = {w: min(loss[(w, S)] for S in Ds) for w in Ws}
    good = {(w, S): (loss[(w, S)] <= own[w] + eps) for w in Ws for S in Ds}
    c_rec = depth_to(Ws, tests, lambda C: len(C) <= 1)
    c_alloc = depth_to(Ws, tests,
                       lambda C: any(all(good[(w, S)] for w in C) for S in Ds))
    return c_rec, c_alloc


def main():
    print("R3 / direction 5: allocation cost versus full-label recovery\n")
    print("PART 1 -- the corpus's compensated D6 world")
    rows = []
    for k in (3,):
        for t0 in (Fr(1, 4), Fr(1, 3)):
            for eps in (Fr(0), Fr(1, 100)):
                cfg, nW, c_rec, c_alloc, Ds, own = part1(k, t0, Fr(1), eps)
                degen = (c_alloc == 0)
                print(f"   k={k} t0={t0} eps={eps}: {nW} worlds, "
                      f"C_recover = {c_rec}, C_allocation = {c_alloc}"
                      + ("   [DEGENERATE: one allocation is already good in every "
                         "world, so nothing has to be learned]" if degen else ""))
                rows.append({"part": 1, "k": k, "t0": str(t0), "eps": str(eps),
                             "worlds": nW, "C_recover": c_rec,
                             "C_allocation": c_alloc, "degenerate": degen})
    print("   => in the D6 construction the separation is real but DEGENERATE: the")
    print("      game has one allocation that is optimal in every world (the pure")
    print("      saddle of scripts/H6_buy_new_reference.py), so the question of")
    print("      'learning which allocation' does not arise there at all. That is the")
    print("      reverse reduction the instruction asked to report rather than hide.\n")

    print("PART 2 -- a family that separates non-degenerately, and its control")
    for fam in (split_family, pinning_family):
        for n in (2, 3, 4, 5):
            name, Ws, Ds, loss, tests = fam(n)
            c_rec, c_alloc = costs(Ws, Ds, loss, tests, Fr(0))
            ratio = (c_alloc / c_rec) if c_rec else None
            print(f"   {name:14s} {len(Ws):3d} worlds: C_recover = {c_rec}, "
                  f"C_allocation = {c_alloc}"
                  + (f"   ratio {float(ratio):.3f}" if ratio is not None else ""))
            rows.append({"part": 2, "family": name, "worlds": len(Ws),
                         "C_recover": c_rec, "C_allocation": c_alloc,
                         "ratio": float(ratio) if ratio is not None else None})
    sp = [r for r in rows if r.get("family", "").startswith("split")]
    pn = [r for r in rows if r.get("family", "").startswith("pinning")]
    print(f"\n   split   : C_allocation stays "
          f"{sorted({r['C_allocation'] for r in sp})} while C_recover grows "
          f"{[r['C_recover'] for r in sp]}  -> the ratio tends to 0, so")
    print(f"             C_allocation = o(C_recover) on this family.")
    print(f"   pinning : C_allocation = C_recover = {[r['C_recover'] for r in pn]}"
          f"  -> no separation, as it must be.")

    print("\nVERDICT")
    print("   The separation EXISTS as a phenomenon and is exhibited with a matching")
    print("   control. It does NOT arise in the corpus's D6 construction, and the")
    print("   reason is structural, not a failure of search: that game has a pure")
    print("   saddle. A version of this direction worth pursuing therefore has to")
    print("   change the construction so the optimal allocation depends on the label.")
    print("   None of this is a delta-PAC sample complexity: only query depth at zero")
    print("   error is computed, so C(q, eps, delta) as written is NOT addressed.")

    out = REPO / "research/worker_R3_d6_20260914/R3_allocation_vs_recovery.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "is C_allocation = o(C_recover_A)?",
        "rows": rows,
        "verdict": "the separation exists and is exhibited with a control, but the "
                   "corpus's D6 construction has a pure saddle so the question "
                   "degenerates there",
        "not_established": [
            "query depth at zero error with deterministic trees; no confidence "
            "parameter appears, so this is NOT C(q, eps, delta)",
            "exact on the listed sizes only",
            "part 2 is a constructed family, not the D6 construction",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
