"""Legal selector for PROTOCOL_HETERO_v0 (Step 3 contract, MARL_HETERO_STEP3_DECISION §A–C).

Information contract: every function here that is used at deployment takes only
  z      : the public scheduler's paid packet cache and time (as a feature vector),
  order  : the base order prepared from z BEFORE the capacity reveal,
  K      : the revealed capacity vector,
  critic : a learned evaluator f_hat(z, K, profile).
No fresh payload, actor action, true value, oracle action list or optimal order enters.

Profiles are lists of m frozensets S_i (receiver i decodes S_i).  One cost function is shared
by every method (single source of truth, also used by the transport):
  patched description : 25*|prefix(order, L0) U  union S_i| + 3 * sum_i |S_i \\ P_i|
  explicit description: 25*|union S_i| + 2*m
  cost = min of the two ("accounted payload/control bytes"; no airtime model).
The common schedule header is identical for all methods and omitted.
"""
from __future__ import annotations
from typing import Callable, List, Sequence
import numpy as np

PAYLOAD_B, PATCH_B, EXPLICIT_B = 25, 3, 2


def prefix_sets(order: Sequence[int], K: Sequence[int]) -> List[frozenset]:
    m = len(order)
    out = []
    for i in range(m):
        seq = [j for j in order if j != i]
        out.append(frozenset(seq[:K[i]]))
    return out


def stream_length(order, P):
    pos = {j: n for n, j in enumerate(order)}
    return max((max(pos[j] for j in s) + 1) if s else 0 for s in P)


def profile_cost(order, K, sets):
    """(bytes, description, transmitted set) for a profile, shared by all methods."""
    m = len(order)
    P = prefix_sets(order, K)
    L0 = stream_length(order, P)
    union = frozenset().union(*sets)
    T_patch = frozenset(order[:L0]) | union
    repl = sum(len(sets[i] - P[i]) for i in range(m))
    b_patch = PAYLOAD_B * len(T_patch) + PATCH_B * repl
    b_expl = PAYLOAD_B * len(union) + EXPLICIT_B * m
    if b_patch <= b_expl:
        return b_patch, 'patched', T_patch
    return b_expl, 'explicit', union


def check_legal(order, K, sets, R=None, cap=None):
    m = len(order)
    P = prefix_sets(order, K)
    for i in range(m):
        s = sets[i]
        if len(s) != K[i] or i in s or not s <= set(range(m)):
            raise ValueError(f'receiver {i}: illegal set {sorted(s)} for capacity {K[i]}')
        if R is not None and len(s - P[i]) > R:
            raise ValueError(f'receiver {i}: {len(s - P[i])} replacements exceed R={R}')
    if cap is not None and profile_cost(order, K, sets)[0] > cap:
        raise ValueError('profile exceeds the byte cap')
    return True


def radius_moves(i, current, P_i, m):
    """All sets within one replacement of the PREFIX (R = 1 family), deterministic order."""
    out = [P_i]
    outside = [b for b in range(m) if b != i and b not in P_i]
    for a in sorted(P_i):
        for b in outside:
            out.append((P_i - {a}) | {b})
    return out


def swap_moves(i, current, P_i, m):
    """Single swaps from the CURRENT set (no radius): the unrestricted budget-aware search."""
    out = [current]
    outside = [b for b in range(m) if b != i and b not in current]
    for a in sorted(current):
        for b in outside:
            out.append((current - {a}) | {b})
    return out


def coordinate_search(order, K, evaluate: Callable, moves: Callable, cap=None, passes=2,
                      call_budget=None):
    """Deterministic best-improvement coordinate search over receivers.

    evaluate(list_of_profiles) -> array of scores.  Starts from the unchanged prefix profile
    (always included).  Infeasible (over-cap) candidates are rejected BEFORE scoring.  Returns
    (profile, score, calls).  This is a local search, not an exact solver.
    """
    m = len(order)
    P = prefix_sets(order, K)
    S = list(P)
    if cap is not None and profile_cost(order, K, S)[0] > cap:
        return None, None, 0                      # the prefix itself is infeasible: report it
    best = float(evaluate([S])[0]); calls = 1
    for _ in range(passes):
        improved = False
        for i in range(m):
            cands = []
            for alt in moves(i, S[i], P[i], m):
                if alt == S[i]:
                    continue
                prof = S[:i] + [frozenset(alt)] + S[i + 1:]
                if cap is not None and profile_cost(order, K, prof)[0] > cap:
                    continue
                cands.append(prof)
            if call_budget is not None:
                cands = cands[:max(0, call_budget - calls)]
            if not cands:
                continue
            vals = np.asarray(evaluate(cands), dtype=float); calls += len(cands)
            j = int(np.argmax(vals))
            if vals[j] > best + 1e-12:
                S, best, improved = cands[j], float(vals[j]), True
        if not improved or (call_budget is not None and calls >= call_budget):
            break
    return S, best, calls


def profile_matrix(sets, m):
    M = np.zeros((m, m), dtype=np.float32)
    for i, s in enumerate(sets):
        for j in s:
            M[i, j] = 1.0
    return M.reshape(-1)


def critic_input(z, K, sets, m):
    return np.concatenate([np.asarray(z, dtype=np.float32), np.asarray(K, dtype=np.float32) / m,
                           profile_matrix(sets, m)])


class HeteroCritic:
    """f_hat(z, K, profile): an MLP on [z, K/m, 9x9 receiver-sender matrix]."""

    def __init__(self, d_in, hidden=128, seed=0):
        import torch
        from torch import nn
        torch.manual_seed(seed)
        self.net = nn.Sequential(nn.Linear(d_in, hidden), nn.ReLU(), nn.Linear(hidden, hidden),
                                 nn.ReLU(), nn.Linear(hidden, 1))
        self.mean = None; self.std = None; self.calls = 0

    def scores(self, z, K, profiles, m):
        import torch
        X = np.stack([critic_input(z, K, p, m) for p in profiles])
        X = (X - self.mean) / self.std
        self.calls += len(profiles)
        with torch.no_grad():
            return self.net(torch.as_tensor(X, dtype=torch.float32)).squeeze(-1).numpy()


def select(method, z, order, K, critic: HeteroCritic, m, cap=None, passes=2):
    """Deployable selection.  method in {'prefix', 'learned_R1', 'direct_unrestricted'}."""
    if method == 'prefix':
        S = prefix_sets(order, K)
        if cap is not None and profile_cost(order, K, S)[0] > cap:
            return None, 0
        return S, 0
    ev = lambda profs: critic.scores(z, K, profs, m)
    moves = radius_moves if method == 'learned_R1' else swap_moves
    S, _, calls = coordinate_search(order, K, ev, moves, cap=cap, passes=passes)
    if S is not None:
        check_legal(order, K, S, R=1 if method == 'learned_R1' else None, cap=cap)
    return S, calls
