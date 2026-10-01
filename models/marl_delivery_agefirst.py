"""AGE-FIRST broadcast order for the Paper-C experiment (30/09 13:0x; ledger L-164).

The relay age diagnostic (L-164) found complete coverage but a long age tail under the cached-queue prefix order: some
senders' own summaries go unbroadcast for many steps.  Paper C ("one exchange suffices", typed frontiers) and ADAPTIVE
(bounded age) suggest bounding the age instead: rank the senders whose last broadcast is OLDEST first, never-broadcast first,
so every sender's fresh summary reaches the head of the stream periodically (round-robin-like).
Legal: it uses only the scheduler context (payloads broadcast in earlier steps, their measurement times), exactly the
information the default cached-queue ranking uses.  Capacities, prefix sets and byte accounting are those of the prefix
rule (HETERO_v0 unchanged).  It is a drop-in for MARL_e3_actor_train_delivery_v7.deliver.
"""
from __future__ import annotations
from models.marl_hetero_selector import prefix_sets


def deliver_agefirst(env, seed, load, t):
    ctx = env.scheduler_context(); P = ctx.packets
    order = tuple(sorted(range(env.n_agents), key=lambda j: (0, j) if P[j] is None else (1, P[j].measured_at, j)))
    env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(env.n_agents)]
    sets = prefix_sets(order, K)
    env.submit_profile([set(s) for s in sets], R=0)
    return sets
