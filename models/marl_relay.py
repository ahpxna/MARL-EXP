"""RELAY-COMPRESSED packets inside PROTOCOL_HETERO_v0 (30/09 11:0x; ledger L-162).

The packet channel is unchanged: every receiver decodes K_i packets of 25 B from the broadcast prefix stream, and the bytes
are accounted exactly as for the prefix.  What changes is the CONTENT of a packet.  Instead of one sender's raw 25 B state
summary, sender k's packet at step t carries 3 B decision summaries (the TRAIN codebook, L = 4) of
  * itself, measured now (fresh), and
  * every other agent it knew at the end of step t-1 (its own inbox and cache then), relayed with their true measurement
    time.
The layout is 1 B header + 8 x 3 B = 25 B, one slot per other agent.

Receiver i at step t merges, for every other agent j:
  * j's own packet if i decoded it this step (fresh);
  * otherwise the most recent copy of j among the relays in the packets i decoded this step and i's own cache.
So a receiver that decodes a single packet already has (possibly one-step-old) summaries of almost every agent.  This is
the completeness the byte-budget variant gave (L-160), obtained inside the packet model.

Information access: a relayed summary is information the relaying sender legitimately held (delivered to it earlier by the
protocol).  The merge uses only packets receiver i decoded plus its own cache.  The relay contents are read from the
senders' own views of the previous step: the simulator composes their packets, and nothing hidden is read.
Two receiver encodings of relayed copies:
  mode 'age'   : relayed copies enter as heard, with their TRUE age (now - measured_at);
  mode 'fresh' : relayed copies are marked as this step's (age 0).  A diagnostic for actors that never saw age > 0.
"""
from __future__ import annotations
from dataclasses import replace


def merge_views(views, prev_views, t, mode='age'):
    """Return a new {i: AgentView} where each receiver's inbox holds its direct packets plus the freshest relayed copy
    of every other agent it did not decode directly; its cache holds nothing that is superseded."""
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
            age = float(v.sim_time) - float(e.measured_at) if mode == 'age' else 0.0
            relayed.append(replace(e, age=age, delivered_step=int(t)))
        out[i] = replace(v, inbox=tuple(direct.values()) + tuple(relayed), cache=())
    return out
