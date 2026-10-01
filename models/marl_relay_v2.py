"""RELAY v2: relay-compressed packets with an EXPLICIT bit layout that fits 25 B (30/09 14:1x; ledger L-171).

L-165 found that v1 (models/marl_relay.py) under-specified the packet.  A broadcast relay packet must carry 9 summaries
(its sender plus the 8 other agents, since every receiver needs a different subset), and v1 handed receivers EXACT ages.
Layout of one 25 B = 200-bit packet, sender k, v1 codebook L = 4, slots ordered by agent id (positional, so no id bits):
  * slot k (the sender itself, measured now): phase 4 + elapsed 1 + vehicles 2 x 4 + waiting 1 x 4 = 17 bits;
  * every other slot j != k: the same 17 bits of the freshest summary k holds of j, plus a 4-bit AGE field in decision
    steps, 0 … 14 = age (saturated at 14), 15 = "no summary of j held" (absent);
  * total 17 + 8 x (17 + 4) = 185 bits <= 200 bits.  The sender's identity is its position in the broadcast stream, which
    the profile description already carries.
The simulation matches this layout:
  * the receiver sees each relayed age as round(age / action interval) steps, SATURATED at 14 steps;
  * a copy older than 14 steps is still delivered, with age 14 (the field cannot say more);
  * the payload fields are quantised by the caller's codebook adapter.
The merge rule is v1's (freshest copy per agent among decoded packets' relays and the receiver's own cache).  Only the
ages the actor sees change.
"""
from __future__ import annotations
from dataclasses import replace

AGE_CAP_STEPS = 14


def merge_views(views, prev_views, t, interval, mode='age', cap=AGE_CAP_STEPS):
    out = {}
    for i, v in views.items():
        direct = {e.sender: e for e in v.inbox}
        best = {}
        cands = list(v.cache)
        if prev_views is not None:
            for k in direct:
                pk = prev_views.get(k)
                if pk is None:
                    continue
                cands += [e for e in pk.inbox if e.sender != i] + [e for e in pk.cache if e.sender != i]
        for e in cands:
            j = e.sender
            if j == i or j in direct:
                continue
            if j not in best or e.measured_at > best[j].measured_at:
                best[j] = e
        relayed = []
        for j, e in best.items():
            if mode == 'age':
                steps = min(cap, int(round((float(v.sim_time) - float(e.measured_at)) / float(interval))))
                age = steps * float(interval)
            else:
                age = 0.0
            relayed.append(replace(e, age=age, delivered_step=int(t)))
        out[i] = replace(v, inbox=tuple(direct.values()) + tuple(relayed), cache=())
    return out
