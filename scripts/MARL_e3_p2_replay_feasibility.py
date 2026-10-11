#!/usr/bin/env python3
"""P2 gate 2 (replay feasibility), trace-only (03/10/2026 18:4x EDT; PAPER1_DESTINATION_AND_CLOSURE Addendum C).
The age-first broadcast order is a function of the capacity trace alone: key(j) = (never broadcast, id) first, then
(time of j's last broadcast, id); T(t) = union over receivers of S_i(t) = the first K_i(t) entries of the order without i;
every j in T(t) is broadcast at t (models/marl_delivery_music.MusicDelivery 'agefirst', envs/external/cityflow_hetero).
No traffic state enters, so the K1 schedule and the iid schedule of an episode can be computed exactly without simulation.
Question: on the upgraded (iid) channel, does receiver i decode the packets the K1 protocol would have given it?
  miss_i(t) = S_i^K1(t) not a subset of S_i^iid(t)   (the iid channel runs its own order);
  miss_i^T(t) = S_i^K1(t) not a subset of T^iid(t)     (not even broadcast to anyone).
Exact receiver-side replay of K1 needs no miss for every receiver from t = 0 (closed loop diverges at the first miss).
Check: the trace reproduces env._trace of one constructed environment exactly (--check-env).
Episodes: development 901-904 and training 301-332 only (the P1 panel 5301-5364 is not read)."""
import argparse, json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import prefix_sets


def trace(seed, load, m, n_dec):
    return np.random.default_rng(5000 + 10 * seed + int(load)).integers(1, m - 1, size=(n_dec, m))


def schedule(K_of_t, m, n_dec):
    last = {}; out = []
    for t in range(n_dec):
        order = tuple(sorted(range(m), key=lambda j: (0, j) if j not in last else (1, last[j], j)))
        S = prefix_sets(order, [int(k) for k in K_of_t(t)]); T = set().union(*S)
        for j in T:
            last[j] = t
        out.append((order, S, T))
    return out


def view_availability(sch_old, sch_new, m, n_dec, slots):
    """Receiver-ONLY exact emulation of the OLD view on the NEW channel, entry level.  The old view of i at t holds, per
    other agent j, the copy measured at table_old[i, j] (AgeMirror replay = the merged view; slot mirror on 4x4).  Receiver i
    can show that copy only if it has SEEN j's copy measured then on the new channel: decoded directly (j in S_i^new(tau)) or
    relayed by a decoded sender k from k's previous table (slot-restricted).  Measurement times depend on the schedule only.
    Returns the share of non-empty old entries available, overall and for direct / relayed entries."""
    from models.marl_delivery_music import AgeMirror, NEVER
    from models.marl_relay_v3 import make_slot_mirror
    Mir = make_slot_mirror(slots) if slots else AgeMirror
    mo, mn = Mir(m), Mir(m); seen = [[set() for _ in range(m)] for _ in range(m)]; ok = tot = okd = totd = 0
    for t in range(n_dec):
        S_new = sch_new[t][1]; prev = mn.table.copy()
        for i in range(m):
            for k in S_new[i]:
                seen[i][k].add(t)
                for j in range(m):
                    if j != i and prev[k, j] > NEVER / 2 and (not slots or j in slots[k]):
                        seen[i][j].add(prev[k, j])
        mo.update(sch_old[t][1], t); mn.update(S_new, t)
        for i in range(m):
            for j in range(m):
                if j == i or mo.table[i, j] <= NEVER / 2:
                    continue
                hit = mo.table[i, j] in seen[i][j]; ok += hit; tot += 1
                if mo.table[i, j] == t:
                    okd += hit; totd += 1
    return dict(all=ok / tot, direct=okd / max(1, totd), relayed=(ok - okd) / max(1, tot - totd))


def main(a):
    from scripts.MARL_hetero_pilot_collect import N_DEC
    from models.marl_relay_v3 import nearest_slots
    res = {}
    for net, m in (('3x3', 9), ('4x4', 16)):
        eps = [(s, h) for s in list(range(901, 905)) + list(range(301, 333)) for h in (8, 16)]
        k1 = schedule(lambda t: [1] * m, m, N_DEC); per = []; first = []; tmiss = []; rr = []; avail = []
        for s, h in eps:
            tr = trace(s, h, m, N_DEC); iid = schedule(lambda t: tr[t], m, N_DEC)
            miss = np.array([[not k1[t][1][i] <= iid[t][1][i] for i in range(m)] for t in range(N_DEC)])
            mT = np.array([[not k1[t][1][i] <= iid[t][2] for i in range(m)] for t in range(N_DEC)])
            per.append(miss.mean()); tmiss.append(mT.mean())
            f = np.where(miss.any(1))[0]; first.append(int(f[0]) if len(f) else N_DEC)
            rr.append(float(np.mean([iid[t][0][0] == k1[t][0][0] for t in range(N_DEC)])))
            if s >= 901:                                   # entry-level availability on the development episodes
                u2 = [(k1[t][0], prefix_sets(k1[t][0], [int(k) for k in tr[t]]), None) for t in range(N_DEC)]
                for t in range(N_DEC):
                    u2[t] = (u2[t][0], u2[t][1], set().union(*u2[t][1]))
                    assert all(k1[t][1][i] <= u2[t][1][i] for i in range(m)), 'U2 must contain the K1 packets'
                sl = nearest_slots(4, 4) if m == 16 else None
                avail.append((view_availability(k1, iid, m, N_DEC, sl), view_availability(k1, u2, m, N_DEC, sl)))
        res[net] = dict(episodes=len(eps), miss_rate=float(np.mean(per)), miss_rate_max=float(np.max(per)),
                        not_broadcast_rate=float(np.mean(tmiss)), first_miss_step_median=float(np.median(first)),
                        first_miss_step_max=int(np.max(first)), position1_agreement=float(np.mean(rr)),
                        k1_T_size=sorted({len(x[2]) for x in k1}),
                        receiver_only_view_availability_U1_iid={k: float(np.mean([x[0][k] for x in avail])) for k in ('all', 'direct', 'relayed')},
                        receiver_only_view_availability_U2_order_preserving={k: float(np.mean([x[1][k] for x in avail])) for k in ('all', 'direct', 'relayed')}, iid_T_size_mean=float(np.mean([len(x[2]) for x in schedule(lambda t: trace(901, 8, m, N_DEC)[t], m, N_DEC)])))
        print(net, json.dumps(res[net]), flush=True)
    if a.check_env:
        import os; os.environ.setdefault('CIG_EXTERNAL_RUNTIME_ACTIVE', '1')
        from scripts.MARL_e3_actor_train import Scenarios
        import tempfile
        sc = Scenarios(Path(tempfile.mkdtemp(dir=a.out))); env, _, _, _ = sc.env(901, 8.0)
        ok = np.array_equal(np.asarray(env._trace), trace(901, 8.0, env.n_agents, N_DEC))
        res['check_env'] = dict(m=env.n_agents, equal=bool(ok)); print('env trace check', ok, 'm', env.n_agents)
        if not ok:
            raise SystemExit('SELF-CHECK FAIL: replicated trace != env._trace')
    Path(a.out).mkdir(parents=True, exist_ok=True); (Path(a.out) / 'replay_feasibility.json').write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', default='research/marl_budget/e3_p2_feasibility_20261003'); p.add_argument('--check-env', action='store_true')
    main(p.parse_args())
