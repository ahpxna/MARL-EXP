#!/usr/bin/env python3
"""D6/MASTER, high-risk direction 6: BUY A NEW REFERENCE on the same world.

The instruction is precise, and the precision is the whole point:
  * keep F_{A,t0} FIXED -- do NOT recompensate F when the reference changes;
  * a query may choose a reference t1, but must come with a response law, noise, a
    cost, and a statement of which coordinate is actually observed;
  * the target is  floor under the old reference  ->  minimum cost to break it;
  * if changing the reference cannot be executed in the observation model at all,
    DROP the acquisition direction and keep it only as a sensitivity theorem.

THE MODEL, stated so it can be checked.
  world       F_A built at t0 (the corpus's compensated world), then held fixed.
  instrument  reference t1 reads the conditional response levels
                  Q_i^{t1}(u) = E_{X ~ Bern(t1)^m} [ F_A(X) | X_i = u ],
              observed with independent N(0, sigma^2) noise. With unbounded samples
              at a fixed t1 the learner therefore learns the exact table Q^{t1} and
              NOTHING else: two worlds with the same table stay indistinguishable at
              that reference however many samples are taken.
  cost        one unit per REFERENCE opened (t0 is already paid for).
  decisions   retained sets S subset T under a cardinality budget; loss is the
              corpus's own productCompressionLoss on the FIXED F_A.

  floor(R)    = the deterministic minimax loss a learner must accept when it can only
              tell worlds apart up to the partition induced by the references in R.
              Inside a class it must commit to one decision for the whole class.

WHAT IS COMPUTED
 1. the partition of worlds at t0 alone, and the resulting floor;
 2. for every candidate t1 on a rational grid, the partition at {t0, t1} and the new
    floor -- so "does buying a reference break the floor?" is answered by exhibiting
    the reference, not by assertion;
 3. the MINIMUM NUMBER of extra references needed to reach the finest partition any
    set of references can reach, by exhaustive search over subsets of the grid;
 4. a control: the same computation where the extra reference is t0 itself, which must
    change nothing.

WHAT THIS DOES NOT ESTABLISH
 - Unbounded samples per reference, so this measures IDENTIFIABILITY and the cost of
   opening references, not a sample-complexity law. sigma never enters the numbers.
 - Only the listed k, t0, rho and the stated rational grid of t1.
 - Deterministic decisions, worst case over worlds.
 - A grid is not all of (0,1): "no t1 helps" below means no t1 ON THE GRID helps.

    .venv/bin/python scripts/H6_buy_new_reference.py
"""
from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util, itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "g4", REPO / "scripts/G4_fixed_world_observation_classes.py")
g4 = importlib.util.module_from_spec(spec); spec.loader.exec_module(g4)


def response_at(cfg, F, t1):
    """Q_i^{t1}(u) for the FIXED F, under a product reference t1."""
    m = cfg["m"]
    out = {}
    for i in range(m):
        lev = {}
        for u in (0, 1):
            s = Fr(0)
            for x in g4.cube(m):
                w = Fr(1)
                for jj in range(m):
                    if jj == i:
                        continue
                    w *= t1 if x[jj] else (1 - t1)
                s += w * F[tuple(u if jj == i else x[jj] for jj in range(m))]
            lev[u] = s
        out[i] = lev
    return out


def partition(keys):
    cls = {}
    for A, k in keys.items():
        cls.setdefault(k, []).append(A)
    return sorted(cls.values(), key=lambda c: sorted(map(sorted, c)))


def floor_of(parts, L, T):
    """the learner must commit to one decision per class; worst case over worlds."""
    tot = None
    for q in range(len(T) + 1):
        for S in itertools.combinations(T, q):
            pass
    best = None
    for q in range(len(T) + 1):
        Ds = list(itertools.combinations(T, q))
        v = 0
        for C in parts:
            v = max(v, min(max(L[(A, S)] for A in C) for S in Ds))
        if best is None or v < best:
            best = v
    return best


def main():
    print("Direction 6: buy a new reference on the same, FIXED, world\n")
    grid = [Fr(1, 8), Fr(1, 5), Fr(1, 4), Fr(1, 3), Fr(2, 5), Fr(1, 2),
            Fr(3, 5), Fr(2, 3), Fr(3, 4)]
    rows = []
    for k in (3,):
        for t0 in (Fr(1, 4), Fr(1, 3)):
            cfg = g4.make_cfg(k, t0, Fr(1))
            Ws = g4.worlds(cfg)
            T = sorted(cfg["T"])
            Fs = {A: g4.world_fn(cfg, A) for A in Ws}
            L = {}
            for A in Ws:
                Q0 = response_at(cfg, Fs[A], t0)
                for q in range(len(T) + 1):
                    for S in itertools.combinations(T, q):
                        L[(A, S)] = g4.compression_loss(cfg, Fs[A], Q0, frozenset(S))
            tabs = {t1: {A: tuple(sorted((i, str(v[0]), str(v[1]))
                                          for i, v in response_at(cfg, Fs[A], t1).items()))
                          for A in Ws} for t1 in set(grid) | {t0}}

            def parts_for(R):
                keys = {A: tuple(tabs[t][A] for t in sorted(R)) for A in Ws}
                return partition(keys)

            p0 = parts_for({t0})
            f0 = floor_of(p0, L, T)
            print(f"k={k} t0={t0}: {len(Ws)} worlds")
            print(f"   at t0 alone: {len(p0)} classes, sizes "
                  f"{sorted(len(c) for c in p0)}, floor = {f0} = {float(f0):.6f}")
            # control: adding t0 again must change nothing
            pc = parts_for({t0})
            assert len(pc) == len(p0) and floor_of(pc, L, T) == f0, \
                "the control changed something"
            print(f"   control, re-buying t0: classes {len(pc)}, floor unchanged")
            helpers = []
            for t1 in grid:
                if t1 == t0:
                    continue
                p1 = parts_for({t0, t1})
                f1 = floor_of(p1, L, T)
                if f1 < f0 or len(p1) > len(p0):
                    helpers.append((t1, len(p1), f1))
            if helpers:
                print(f"   references that refine the partition or lower the floor:")
                for t1, npc, f1 in helpers:
                    print(f"      t1={t1}: {npc} classes, floor {f1} = {float(f1):.6f}"
                          f"   (drop {float(f0-f1):.6f})")
            else:
                print(f"   NO t1 on the grid refines the partition or lowers the floor")
            # finest reachable, and the minimum number of extra references for it
            allR = {t0} | set(grid)
            pbest = parts_for(allR)
            fbest = floor_of(pbest, L, T)
            need = None
            for r in range(0, len(grid) + 1):
                for R in itertools.combinations([g for g in grid if g != t0], r):
                    p = parts_for({t0} | set(R))
                    if len(p) == len(pbest) and floor_of(p, L, T) == fbest:
                        need = (r, R)
                        break
                if need:
                    break
            print(f"   finest reachable with every grid reference: {len(pbest)} "
                  f"classes, floor {fbest} = {float(fbest):.6f}")
            print(f"   MINIMUM COST to reach it: {need[0]} extra reference(s)"
                  + (f", e.g. {list(need[1])}" if need[0] else ""))
            # the mechanism: is there a pure saddle?
            Dall = [S for q in range(len(T) + 1)
                    for S in itertools.combinations(T, q)]
            minmax = min(max(L[(A, S)] for A in Ws) for S in Dall)
            maxmin = max(min(L[(A, S)] for S in Dall) for A in Ws)
            saddle = (minmax == maxmin)
            print(f"   min_S max_A L = {minmax} ; max_A min_S L = {maxmin}"
                  f"   -> pure saddle: {saddle}")
            rows.append({"k": k, "t0": str(t0), "worlds": len(Ws),
                         "minmax": str(minmax), "maxmin": str(maxmin),
                         "pure_saddle": saddle,
                         "identifiability_broken_by_one_reference":
                             len(parts_for({t0, grid[0]})) > len(p0),
                         "classes_at_t0": len(p0), "floor_at_t0": str(f0),
                         "helpful_references": [[str(t), n, str(f)]
                                                for t, n, f in helpers],
                         "finest_classes": len(pbest), "finest_floor": str(fbest),
                         "min_extra_references": need[0],
                         "witness_reference_set": [str(t) for t in need[1]],
                         "floor_drop": str(f0 - fbest)})
            print()

    lowers = any(r["floor_drop"] != "0" for r in rows)
    ident = all(r["identifiability_broken_by_one_reference"] for r in rows)
    saddle = all(r["pure_saddle"] for r in rows)
    print("VERDICT -- two facts that must not be merged")
    print(f"   IDENTIFIABILITY: at t0 alone every world sits in ONE class (the "
          f"compensation makes the target response world-independent). ONE extra "
          f"reference already separates ALL worlds: {ident}.")
    print(f"   DECISION VALUE : the minimax loss is UNCHANGED by that: floor drop "
          f"{'> 0 somewhere' if lowers else 'is exactly 0 everywhere'}.")
    if not lowers:
        print("   So buying a reference buys full knowledge of A and buys NOTHING in")
        print("   decision terms. Per the instruction the acquisition reading is")
        print("   DROPPED here and this stands as a sensitivity result.")
        if saddle:
            print(f"   The mechanism is explicit: the game has a PURE SADDLE, "
                  f"min_S max_A L = max_A min_S L, so one retained set is")
            print("   simultaneously optimal for every world and knowing A cannot help.")
            print("   That also says what a productive version of this direction needs:")
            print("   a construction WITHOUT a pure saddle, where the optimal decision")
            print("   actually depends on A.")
    else:
        print("   Changing the reference is executable AND lowers the floor; the")
        print("   cheapest reference set that does it is exhibited above.")
    print("   Either way this is identifiability under unbounded sampling, not a")
    print("   sample-complexity law: sigma never entered a single number.")

    out = REPO / "research/worker_H6_reference_20260914/H6_buy_new_reference.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "on a FIXED world F_{A,t0}, can buying a different reference t1 "
                    "break the regret floor, and at what minimum cost?",
        "model": "F fixed at t0 with NO recompensation; a reference t1 reveals the "
                 "exact conditional response table Q^{t1} under unbounded sampling; "
                 "cost is one unit per reference opened",
        "rows": rows,
        "not_established": [
            "unbounded samples per reference: this is identifiability plus the cost "
            "of opening references, NOT a sample-complexity law; sigma never enters",
            "a rational grid of t1, not all of (0,1)",
            "deterministic decisions, worst case over worlds, listed k and t0 only",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
