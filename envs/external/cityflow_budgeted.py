"""Budgeted-communication CityFlow environment (P3, PROTOCOL_v0).

The message budget is enforced at INFORMATION ACCESS.  Agent ``i`` (an
intersection) sees only:

* its own incoming-lane sensor (fresh, every decision step);
* the bytes of messages actually transmitted to it, decoded;
* for every other neighbour, the last message it received from that neighbour,
  with its measurement timestamp and age, or nothing if it never heard it;
* the budget ``k_t``, and only after it committed a ranking at step ``t``;
* public static topology (``public_topology(i)``).

Nothing else is placed in an :class:`AgentView`.  Views are immutable and hold
only numbers, strings, tuples and read-only arrays: no engine or environment
reference escapes to a policy.

Protocol per decision step (enforced by a stage machine; any other order raises)::

    views()          stage "rank"      own sensor + cache, budget hidden
    commit_rankings  -> stage "reveal" permutation of N(i) for every agent
    reveal_budget    -> stage "revise" k_t revealed
    submit_final_sets-> stage "transmit" |T|=min(k,|N(i)|), |prefix_k \\ T| <= R
    transmit         -> stage "act"    sender summaries encoded to bytes, delivered
    step(actions)    -> stage "rank" (or "done")

Differences from ``envs/external/cityflow.py`` (not edited):

* The sensor there is built from ``item["roads"]``, which holds incoming AND
  outgoing roads.  Neighbour observations therefore overlap.  Its
  ``relation_features(ego, j)`` also reads the neighbour's FRESH observation.
  Here a sensor covers only the intersection's own incoming lanes.  Sensors are
  disjoint, and downstream occupancy reaches ``i`` only through messages.
* Invalid actions raise instead of being remapped silently.

Oracle access (``mode="oracle"``) serves explicitly labelled diagnostics:
counterfactual views, all-neighbour payloads, clone/restore rollouts.  In
``mode="deploy"`` every oracle entry point raises ``PermissionError``.  Every
oracle call is counted in ``access_log``.

This module imports ``cityflow`` only inside :func:`make_budgeted_grid_env`.
The dependency-free parts (codec, traces, views, stage machine) run in the
main venv against an engine double.
"""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import math
import os
import struct
import time
from dataclasses import dataclass, fields, is_dataclass
from pathlib import Path
from typing import Dict, List, Mapping, Optional, Sequence, Tuple

import numpy as np

N_SLOTS = 4  # approach slots: 0 eastbound, 1 northbound, 2 westbound, 3 southbound
PAYLOAD_FORMAT = "<HIBH8H"  # sender, measured_at, phase, phase_elapsed, 4x(vehicles, waiting)
PAYLOAD_BYTES = struct.calcsize(PAYLOAD_FORMAT)  # 25
REQUEST_FORMAT = "<HHI"  # receiver, sender, decision step
REQUEST_BYTES = struct.calcsize(REQUEST_FORMAT)  # 8
UINT16_MAX = 65535
UINT8_MAX = 255
STAGES = ("rank", "reveal", "revise", "transmit", "act", "done")


# ---------------------------------------------------------------------------
# Messages
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MessagePayload:
    """A neighbour's local summary, as decoded from its bytes."""
    sender: int
    measured_at: int  # integer simulator seconds
    phase: int
    phase_elapsed: int  # seconds since the sender's last phase change
    vehicles: Tuple[int, ...]  # per approach slot, summed over lanes
    waiting: Tuple[int, ...]  # per approach slot, summed over lanes


def _clip(value: float, hi: int) -> Tuple[int, int]:
    v = int(round(float(value)))
    if v < 0:
        return 0, 1
    if v > hi:
        return hi, 1
    return v, 0


def encode_payload(p: MessagePayload) -> Tuple[bytes, int]:
    """Serialise a payload to exactly PAYLOAD_BYTES bytes; returns (bytes, n_clipped)."""
    if len(p.vehicles) != N_SLOTS or len(p.waiting) != N_SLOTS:
        raise ValueError("payload must carry one value per approach slot")
    clipped = 0
    vals = []
    for raw, hi in ((p.sender, UINT16_MAX),):
        v, c = _clip(raw, hi); vals.append(v); clipped += c
    measured = int(p.measured_at)
    if not 0 <= measured <= 0xFFFFFFFF:
        raise ValueError("measured_at outside uint32")
    vals.append(measured)
    for raw, hi in ((p.phase, UINT8_MAX), (p.phase_elapsed, UINT16_MAX)):
        v, c = _clip(raw, hi); vals.append(v); clipped += c
    for s in range(N_SLOTS):
        for raw in (p.vehicles[s], p.waiting[s]):
            v, c = _clip(raw, UINT16_MAX); vals.append(v); clipped += c
    return struct.pack(PAYLOAD_FORMAT, *vals), clipped


def decode_payload(data: bytes) -> MessagePayload:
    if len(data) != PAYLOAD_BYTES:
        raise ValueError(f"payload must be {PAYLOAD_BYTES} bytes, got {len(data)}")
    v = struct.unpack(PAYLOAD_FORMAT, data)
    sender, measured, phase, elapsed = v[0], v[1], v[2], v[3]
    rest = v[4:]
    return MessagePayload(int(sender), int(measured), int(phase), int(elapsed),
                          tuple(int(rest[2 * s]) for s in range(N_SLOTS)),
                          tuple(int(rest[2 * s + 1]) for s in range(N_SLOTS)))


# ---------------------------------------------------------------------------
# Budget traces
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BudgetTraceSpec:
    """Budget process k_t (messages agent i may RECEIVE at decision step t).

    kind:
      "fixed"       k_t = k.
      "drops"       k_t = k except in drop episodes; a drop starts with probability
                    p_drop per step, lasts Geometric(1/drop_len_mean) steps, k_t = k_low.
      "bursty"      Gilbert-Elliott two-state chain: good -> k, bad -> k_low,
                    P(good->bad)=p_gb, P(bad->good)=p_bg, starting in good.
      "per_episode" k drawn once per episode uniformly from k_choices.
    per_agent: independent streams per receiver (default: one common trace).
    """
    kind: str = "fixed"
    k: int = 1
    k_low: int = 0
    p_drop: float = 0.1
    drop_len_mean: float = 3.0
    p_gb: float = 0.2
    p_bg: float = 0.3
    k_choices: Tuple[int, ...] = (0, 1, 2, 3, 4)
    per_agent: bool = False

    def as_dict(self):
        return {f.name: getattr(self, f.name) for f in fields(self)}


def generate_budget_trace(spec: BudgetTraceSpec, n_steps: int, n_agents: int, seed: int) -> np.ndarray:
    """Return an int array (n_steps, n_agents).  Deterministic in (spec, seed)."""
    n_steps, n_agents = int(n_steps), int(n_agents)
    streams = n_agents if spec.per_agent else 1
    out = np.zeros((n_steps, streams), dtype=np.int64)
    for s in range(streams):
        rng = np.random.default_rng([int(seed), s, 0xB0D6])
        if spec.kind == "fixed":
            out[:, s] = int(spec.k)
        elif spec.kind == "drops":
            t = 0
            while t < n_steps:
                if rng.random() < float(spec.p_drop):
                    length = int(rng.geometric(1.0 / max(1.0, float(spec.drop_len_mean))))
                    out[t:t + length, s] = int(spec.k_low)
                    t += length
                else:
                    out[t, s] = int(spec.k)
                    t += 1
        elif spec.kind == "bursty":
            good = True
            for t in range(n_steps):
                out[t, s] = int(spec.k) if good else int(spec.k_low)
                u = rng.random()
                good = (u >= float(spec.p_gb)) if good else (u < float(spec.p_bg))
        elif spec.kind == "per_episode":
            out[:, s] = int(rng.choice(np.asarray(spec.k_choices, dtype=np.int64)))
        else:
            raise ValueError(f"unknown budget trace kind {spec.kind!r}")
    if (out < 0).any():
        raise ValueError("budget must be nonnegative")
    if not spec.per_agent:
        out = np.repeat(out, n_agents, axis=1)
    return out


# ---------------------------------------------------------------------------
# Views and topology
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CacheEntry:
    sender: int
    payload: MessagePayload
    measured_at: int
    age: float  # sim seconds between measurement and the view's time
    delivered_step: int


@dataclass(frozen=True)
class AgentView:
    """Everything agent i may use at one stage of one decision step."""
    agent: int
    decision_step: int
    sim_time: float
    stage: str
    lane_vehicles: np.ndarray  # (N_SLOTS, L) own incoming lanes, read-only
    lane_waiting: np.ndarray
    own_phase: int
    own_phase_elapsed: float
    neighbours: Tuple[int, ...]
    inbox: Tuple[CacheEntry, ...]  # delivered at this step (after transmit only)
    cache: Tuple[CacheEntry, ...]  # older messages from neighbours not in inbox
    never_heard: Tuple[int, ...]
    budget: Optional[int]  # None before the reveal
    budget_history: Tuple[int, ...]  # k_0 .. k_{t-1}
    committed_ranking: Optional[Tuple[int, ...]]
    final_set: Optional[Tuple[int, ...]]
    R: Optional[int]  # revision allowance, public protocol constant

    def message_from(self, j: int) -> Optional[CacheEntry]:
        for e in self.inbox:
            if e.sender == j:
                return e
        for e in self.cache:
            if e.sender == j:
                return e
        return None

    def flat_obs(self) -> np.ndarray:
        return np.concatenate([self.lane_vehicles.ravel(), self.lane_waiting.ravel(),
                               np.asarray([self.own_phase, self.own_phase_elapsed], dtype=np.float32)])


@dataclass(frozen=True)
class PublicTopology:
    """Static facts about intersection i.  Public: no dynamic neighbour state."""
    agent: int
    intersection_id: str
    neighbours: Tuple[int, ...]
    incoming_roads: Tuple[Optional[str], ...]  # per slot
    lanes_per_slot: Tuple[int, ...]
    outgoing: Tuple[Tuple[str, Optional[int], Optional[int]], ...]  # (road, receiver j, slot at j)
    n_phases: int
    valid_phases: Tuple[int, ...]
    phase_movements: Tuple[Tuple[Tuple[int, str], ...], ...]  # per phase: (incoming slot, outgoing road)


def _readonly(a: np.ndarray) -> np.ndarray:
    a = np.array(a, dtype=np.float32, copy=True)
    a.setflags(write=False)
    return a


def iter_view_leaves(obj, path="view"):
    """Yield (path, leaf) for every leaf of a view (tests / audits)."""
    if is_dataclass(obj) and not isinstance(obj, type):
        for f in fields(obj):
            yield from iter_view_leaves(getattr(obj, f.name), f"{path}.{f.name}")
    elif isinstance(obj, (tuple, list)):
        for k, v in enumerate(obj):
            yield from iter_view_leaves(v, f"{path}[{k}]")
    elif isinstance(obj, dict):
        for k, v in sorted(obj.items(), key=lambda kv: repr(kv[0])):
            yield from iter_view_leaves(v, f"{path}{{{k!r}}}")
    else:
        yield path, obj


def canonical_view_bytes(view: AgentView) -> bytes:
    """A canonical serialisation: equal bytes iff equal views (for non-interference tests)."""
    parts = []
    for path, leaf in iter_view_leaves(view):
        if isinstance(leaf, np.ndarray):
            parts.append(f"{path}=nd{leaf.shape}{leaf.dtype}:".encode() + leaf.tobytes())
        else:
            parts.append(f"{path}={type(leaf).__name__}:{leaf!r}".encode())
    return b"\x00".join(parts)


def view_fingerprint(view: AgentView) -> str:
    return hashlib.sha256(canonical_view_bytes(view)).hexdigest()


# ---------------------------------------------------------------------------
# Environment
# ---------------------------------------------------------------------------

def _slot_of_road(road: dict) -> int:
    pts = road.get("points") or []
    if len(pts) < 2:
        raise ValueError(f"road {road.get('id')} has no geometry to orient its approach")
    (x0, y0), (x1, y1) = (pts[-2]["x"], pts[-2]["y"]), (pts[-1]["x"], pts[-1]["y"])
    theta = math.atan2(float(y1) - float(y0), float(x1) - float(x0))
    return int(round(theta / (math.pi / 2.0))) % N_SLOTS


class BudgetedCityFlowEnv:
    """CityFlow signal control with a receiver-side message budget (see module doc)."""

    def __init__(self, engine, roadnet: dict, *, budget_spec: BudgetTraceSpec, R: Optional[int],
                 n_decisions: int, action_interval: int = 10, delivery_delay: int = 0,
                 mode: str = "deploy", clearance_phase: Optional[int] = 0):
        if mode not in ("deploy", "oracle"):
            raise ValueError("mode must be 'deploy' or 'oracle'")
        if R is not None and int(R) < 0:
            raise ValueError("R must be None (unrestricted) or >= 0")
        self._engine = engine
        self.mode = mode
        self.R = None if R is None else int(R)
        self.budget_spec = budget_spec
        self.n_decisions = int(n_decisions)
        self.action_interval = int(action_interval)
        self.delivery_delay = int(delivery_delay)
        if self.delivery_delay < 0 or self.action_interval < 1 or self.n_decisions < 1:
            raise ValueError("invalid timing parameters")
        self._parse_roadnet(roadnet, clearance_phase)
        self.access_log = {"oracle_payloads": 0, "counterfactual_view": 0, "oracle_rollout": 0,
                           "clone_state": 0}
        self._stage = "need_reset"

    # ----- static structure -------------------------------------------------
    def _parse_roadnet(self, roadnet, clearance_phase):
        inters = sorted((x for x in roadnet.get("intersections", []) if not x.get("virtual", False)),
                        key=lambda x: str(x["id"]))
        if not inters:
            raise RuntimeError("roadnet has no controllable intersections")
        self.agent_ids = [str(x["id"]) for x in inters]
        self.n_agents = len(self.agent_ids)
        index = {iid: k for k, iid in enumerate(self.agent_ids)}
        roads = {str(r["id"]): r for r in roadnet.get("roads", [])}
        self._incoming: List[List[Optional[str]]] = [[None] * N_SLOTS for _ in range(self.n_agents)]
        self._slot_at_end: Dict[str, int] = {}
        nbrs = [set() for _ in range(self.n_agents)]
        outgoing = [[] for _ in range(self.n_agents)]
        for rid, road in roads.items():
            a, b = str(road["startIntersection"]), str(road["endIntersection"])
            if b in index:
                slot = _slot_of_road(road)
                if self._incoming[index[b]][slot] is not None:
                    raise ValueError(f"two incoming roads of {b} share approach slot {slot}")
                self._incoming[index[b]][slot] = rid
                self._slot_at_end[rid] = slot
            if a in index and b in index and a != b:
                nbrs[index[a]].add(index[b]); nbrs[index[b]].add(index[a])
        for rid, road in roads.items():
            a, b = str(road["startIntersection"]), str(road["endIntersection"])
            if a in index:
                j = index.get(b)
                outgoing[index[a]].append((rid, j, self._slot_at_end.get(rid) if j is not None else None))
        self._lanes: List[List[Tuple[str, ...]]] = []
        L = 1
        for i in range(self.n_agents):
            per_slot = []
            for rid in self._incoming[i]:
                if rid is None:
                    per_slot.append(())
                else:
                    n = len(roads[rid].get("lanes", [])) or 1
                    per_slot.append(tuple(f"{rid}_{k}" for k in range(n)))
                    L = max(L, n)
            self._lanes.append(per_slot)
        self.max_lanes = L
        self.neighbours: Tuple[Tuple[int, ...], ...] = tuple(tuple(sorted(s)) for s in nbrs)
        self._topology = []
        for i, item in enumerate(inters):
            tl = item.get("trafficLight", {})
            phases = tl.get("lightphases", []) or [{}]
            links = item.get("roadLinks", [])
            movements = []
            for ph in phases:
                mv = []
                for li in ph.get("availableRoadLinks", []):
                    link = links[int(li)]
                    s_road = str(link["startRoad"])
                    if s_road in self._slot_at_end:
                        mv.append((self._slot_at_end[s_road], str(link["endRoad"])))
                movements.append(tuple(mv))
            n_ph = len(phases)
            valid = tuple(p for p in range(n_ph) if not (n_ph > 1 and clearance_phase is not None
                                                          and p == int(clearance_phase)))
            self._topology.append(PublicTopology(
                agent=i, intersection_id=self.agent_ids[i], neighbours=self.neighbours[i],
                incoming_roads=tuple(self._incoming[i]),
                lanes_per_slot=tuple(len(x) for x in self._lanes[i]),
                outgoing=tuple(sorted(outgoing[i], key=lambda t: t[0])), n_phases=n_ph,
                valid_phases=valid, phase_movements=tuple(movements)))

    def public_topology(self, i: int) -> PublicTopology:
        return self._topology[int(i)]

    # ----- stage machine ----------------------------------------------------
    def _require(self, stage: str):
        if self._stage != stage:
            raise RuntimeError(f"protocol violation: expected stage {stage!r}, env is at {self._stage!r}")

    @property
    def stage(self) -> str:
        return self._stage

    @property
    def decision_step(self) -> int:
        return self._t

    def reset(self, budget_seed: int = 0) -> Dict[int, AgentView]:
        try:
            self._engine.reset(seed=True)
        except TypeError:
            self._engine.reset()
        self._t = 0
        self._trace = generate_budget_trace(self.budget_spec, self.n_decisions, self.n_agents, budget_seed)
        self._phase = [self._topology[i].valid_phases[0] for i in range(self.n_agents)]
        self._phase_since = [0.0] * self.n_agents
        for i, iid in enumerate(self.agent_ids):
            self._engine.set_tl_phase(iid, int(self._phase[i]))
        self._cache: List[Dict[int, Tuple[MessagePayload, int, int]]] = [dict() for _ in range(self.n_agents)]
        self._pending: List[Tuple[int, int, int, bytes]] = []  # (deliver_step, receiver, sender, bytes)
        self._budget_hist: List[List[int]] = [[] for _ in range(self.n_agents)]
        self._rankings = None
        self._k = None
        self._final = None
        self._revisions = None
        self._delivered_now: List[set] = [set() for _ in range(self.n_agents)]
        self.step_records: List[dict] = []
        self.commit_hashes: List[str] = []
        self._totals = {"payload_bytes": 0, "request_bytes": 0, "messages": 0, "clipped_fields": 0,
                        "revisions": 0, "decisions": 0}
        self._first_seen: Dict[str, float] = {}
        self._finished_tt: List[float] = []
        self._done_ids: set = set()
        self._running: set = set()
        self._queue_trace: List[float] = []
        self._comm_record = {}
        self._read_lanes()
        self._track_vehicles()
        self._stage = "rank"
        return self.views()

    def _now(self) -> float:
        return float(self._engine.get_current_time())

    def _read_lanes(self):
        self._lane_veh = dict(self._engine.get_lane_vehicle_count())
        self._lane_wait = dict(self._engine.get_lane_waiting_vehicle_count())
        self._lanes_time = self._now()

    def _sensor(self, i: int) -> Tuple[np.ndarray, np.ndarray]:
        """Intersection i's own incoming-lane detectors.  Only i's lanes are read."""
        veh = np.zeros((N_SLOTS, self.max_lanes), dtype=np.float32)
        wait = np.zeros((N_SLOTS, self.max_lanes), dtype=np.float32)
        for s, lanes in enumerate(self._lanes[i]):
            for k, lane in enumerate(lanes):
                veh[s, k] = float(self._lane_veh.get(lane, 0.0))
                wait[s, k] = float(self._lane_wait.get(lane, 0.0))
        return veh, wait

    def _summary(self, j: int) -> MessagePayload:
        """Sender j's local summary at the current time (computed by j from j's sensor)."""
        veh, wait = self._sensor(j)
        now = self._now()
        return MessagePayload(
            sender=int(j), measured_at=int(round(now)), phase=int(self._phase[j]),
            phase_elapsed=int(round(now - self._phase_since[j])),
            vehicles=tuple(int(round(v)) for v in veh.sum(axis=1)),
            waiting=tuple(int(round(v)) for v in wait.sum(axis=1)))

    def _build_view(self, i: int, *, inbox_override: Optional[Dict[int, MessagePayload]] = None) -> AgentView:
        i = int(i)
        now = self._now()
        veh, wait = self._sensor(i)
        stage = self._stage
        post_reveal = stage in ("revise", "transmit", "act")
        inbox, cache, never = [], [], []
        delivered = self._delivered_now[i] if stage == "act" else set()
        for j in self.neighbours[i]:
            if inbox_override is not None and j in inbox_override:
                p = inbox_override[j]
                inbox.append(CacheEntry(j, p, p.measured_at, now - p.measured_at, self._t))
                continue
            entry = self._cache[i].get(j)
            if entry is None:
                never.append(j)
                continue
            p, measured, dstep = entry
            ce = CacheEntry(j, p, measured, now - measured, dstep)
            if j in delivered and dstep == self._t and inbox_override is None:
                inbox.append(ce)
            else:
                cache.append(ce)
        return AgentView(
            agent=i, decision_step=self._t, sim_time=now, stage=stage,
            lane_vehicles=_readonly(veh), lane_waiting=_readonly(wait),
            own_phase=int(self._phase[i]), own_phase_elapsed=float(now - self._phase_since[i]),
            neighbours=self.neighbours[i], inbox=tuple(inbox), cache=tuple(cache),
            never_heard=tuple(never),
            budget=int(self._k[i]) if (post_reveal and self._k is not None) else None,
            budget_history=tuple(self._budget_hist[i]),
            committed_ranking=tuple(self._rankings[i]) if (self._rankings is not None and stage != "rank") else None,
            final_set=tuple(self._final[i]) if (self._final is not None and stage == "act") else None,
            R=self.R)

    def views(self) -> Dict[int, AgentView]:
        if self._stage in ("need_reset", "done"):
            raise RuntimeError(f"no views at stage {self._stage!r}")
        return {i: self._build_view(i) for i in range(self.n_agents)}

    def commit_rankings(self, rankings: Mapping[int, Sequence[int]]) -> str:
        self._require("rank")
        fixed = {}
        for i in range(self.n_agents):
            if i not in rankings:
                raise ValueError(f"missing ranking for agent {i}")
            r = tuple(int(x) for x in rankings[i])
            if sorted(r) != list(self.neighbours[i]) or len(set(r)) != len(r):
                raise ValueError(f"ranking of agent {i} must be a permutation of its neighbours {self.neighbours[i]}")
            fixed[i] = r
        self._rankings = fixed
        digest = hashlib.sha256(json.dumps([self._t, [fixed[i] for i in range(self.n_agents)]]).encode()).hexdigest()
        self.commit_hashes.append(digest)
        self._stage = "reveal"
        return digest

    def reveal_budget(self) -> Dict[int, int]:
        self._require("reveal")
        self._k = {i: int(self._trace[self._t, i]) for i in range(self.n_agents)}
        self._stage = "revise"
        return dict(self._k)

    def submit_final_sets(self, final_sets: Mapping[int, Sequence[int]]) -> Dict[int, int]:
        self._require("revise")
        out, revs = {}, {}
        for i in range(self.n_agents):
            if i not in final_sets:
                raise ValueError(f"missing final set for agent {i}")
            T = tuple(int(x) for x in final_sets[i])
            if len(set(T)) != len(T) or not set(T) <= set(self.neighbours[i]):
                raise ValueError(f"final set of agent {i} must be distinct neighbours")
            size = min(self._k[i], len(self.neighbours[i]))
            if len(T) != size:
                raise ValueError(f"agent {i}: |T|={len(T)} but min(k, |N|)={size}")
            prefix = set(self._rankings[i][:size])
            r = len(prefix - set(T))
            if self.R is not None and r > self.R:
                raise ValueError(f"agent {i}: {r} replacements exceed R={self.R}")
            out[i] = tuple(sorted(T)); revs[i] = r
        self._final, self._revisions = out, revs
        self._stage = "transmit"
        return dict(revs)

    def transmit(self) -> Dict[int, AgentView]:
        self._require("transmit")
        rec = {"payload_bytes": 0, "request_bytes": 0, "messages": 0, "clipped_fields": 0}
        for i in range(self.n_agents):
            for j in self._final[i]:
                payload, clipped = encode_payload(self._summary(j))
                rec["request_bytes"] += REQUEST_BYTES
                rec["payload_bytes"] += len(payload)
                rec["messages"] += 1
                rec["clipped_fields"] += clipped
                self._pending.append((self._t + self.delivery_delay, i, j, payload))
        self._delivered_now = [set() for _ in range(self.n_agents)]
        keep = []
        for (dstep, i, j, data) in self._pending:
            if dstep != self._t:
                keep.append((dstep, i, j, data))
                continue
            p = decode_payload(data)
            if p.sender != j:
                raise RuntimeError("decoded sender does not match the transmitting neighbour")
            old = self._cache[i].get(j)
            if old is None or p.measured_at >= old[1]:
                self._cache[i][j] = (p, p.measured_at, self._t)
            self._delivered_now[i].add(j)
        self._pending = keep
        for key in rec:
            self._totals[key] += rec[key]
        self._comm_record = rec
        self._stage = "act"
        return self.views()

    def valid_action_mask(self, i: int) -> np.ndarray:
        topo = self._topology[int(i)]
        m = np.zeros((topo.n_phases,), dtype=bool)
        m[list(topo.valid_phases)] = True
        return m

    def _track_vehicles(self):
        """Per simulator second: entry = first time seen running, exit = first time absent."""
        now = self._now()
        current = set(self._engine.get_vehicles(include_waiting=False))
        for vid in current:
            if vid not in self._first_seen:
                self._first_seen[vid] = now
        for vid in list(self._running - current):
            if vid not in self._done_ids:
                self._done_ids.add(vid)
                self._finished_tt.append(now - self._first_seen[vid])
        self._running = current

    def _total_waiting(self) -> float:
        return float(sum(self._lane_wait.get(l, 0.0) for i in range(self.n_agents)
                         for lanes in self._lanes[i] for l in lanes))

    def step(self, actions: Mapping[int, int]):
        self._require("act")
        for i in range(self.n_agents):
            if i not in actions:
                raise ValueError(f"missing action for agent {i}")
            a = int(actions[i])
            if a not in self._topology[i].valid_phases:
                raise ValueError(f"agent {i}: phase {a} not in valid phases {self._topology[i].valid_phases}")
        stale_ages, never = [], 0
        for i in range(self.n_agents):
            for j in self.neighbours[i]:
                if j in self._delivered_now[i]:
                    continue
                entry = self._cache[i].get(j)
                if entry is None:
                    never += 1
                else:
                    stale_ages.append(self._now() - entry[1])
        now = self._now()
        for i, iid in enumerate(self.agent_ids):
            a = int(actions[i])
            if a != self._phase[i]:
                self._phase[i] = a
                self._phase_since[i] = now
            self._engine.set_tl_phase(iid, a)
        for _ in range(self.action_interval):
            self._engine.next_step()
            self._track_vehicles()
        for i in range(self.n_agents):
            self._budget_hist[i].append(int(self._k[i]))
        self._read_lanes()
        rewards = {}
        for i in range(self.n_agents):
            _, wait = self._sensor(i)
            rewards[i] = -float(wait.sum())
        queue = self._total_waiting()
        self._queue_trace.append(queue)
        rec = dict(self._comm_record)
        rec.update({
            "t": self._t, "budget": [int(self._k[i]) for i in range(self.n_agents)],
            "revisions": int(sum(self._revisions.values())), "queue": queue,
            "stale_age_mean": float(np.mean(stale_ages)) if stale_ages else 0.0,
            "stale_age_max": float(np.max(stale_ages)) if stale_ages else 0.0,
            "never_heard_pairs": int(never), "running": len(self._running),
            "finished": len(self._finished_tt)})
        self._totals["revisions"] += rec["revisions"]
        self._totals["decisions"] += 1
        self.step_records.append(rec)
        self._t += 1
        self._rankings = self._k = self._final = self._revisions = None
        self._delivered_now = [set() for _ in range(self.n_agents)]
        self._stage = "done" if self._t >= self.n_decisions else "rank"
        return rewards, self._stage == "done", rec

    def episode_summary(self) -> dict:
        tt = self._finished_tt
        censored = None
        if hasattr(self._engine, "get_average_travel_time"):
            censored = float(self._engine.get_average_travel_time())
        stale = [r["stale_age_mean"] for r in self.step_records]
        return {
            "decisions": self._totals["decisions"],
            "sim_seconds": self._now(),
            "finished_vehicles": len(tt),
            "unfinished_vehicles": len(self._running),
            "throughput_per_hour": 3600.0 * len(tt) / max(1.0, self._now()),
            "travel_time_finished_mean": float(np.mean(tt)) if tt else None,
            "travel_time_cityflow_censored": censored,
            "queue_mean": float(np.mean(self._queue_trace)) if self._queue_trace else None,
            "payload_bytes": self._totals["payload_bytes"],
            "request_bytes": self._totals["request_bytes"],
            "messages": self._totals["messages"],
            "clipped_fields": self._totals["clipped_fields"],
            "revisions": self._totals["revisions"],
            "stale_age_mean_over_steps": float(np.mean(stale)) if stale else None,
            "access_log": dict(self.access_log),
            "oracle_access_used": any(v > 0 for v in self.access_log.values()),
        }

    # ----- invariants (audit) ------------------------------------------------
    def check_access_invariants(self, views: Mapping[int, AgentView]) -> List[str]:
        """Structural checks on views; returns a list of violations (empty = pass)."""
        bad = []
        now = self._now()
        for i, v in views.items():
            if set(e.sender for e in v.inbox) - set(self.neighbours[i]):
                bad.append(f"agent {i}: inbox sender outside N(i)")
            if v.stage != "act" and v.inbox:
                bad.append(f"agent {i}: inbox before transmission")
            if v.stage == "act" and self.delivery_delay == 0 and self._final is not None:
                if not set(e.sender for e in v.inbox) <= set(self._final[i]):
                    bad.append(f"agent {i}: inbox sender not in its final set")
            for e in v.cache:
                if e.measured_at >= now and e.delivered_step != self._t:
                    bad.append(f"agent {i}: cache entry from {e.sender} is not older than now")
                if v.stage == "act" and e.sender in self._delivered_now[i]:
                    bad.append(f"agent {i}: delivered sender {e.sender} listed as cache")
            if v.stage in ("rank", "reveal") and v.budget is not None:
                bad.append(f"agent {i}: budget visible before the reveal")
            for path, leaf in iter_view_leaves(v):
                if not isinstance(leaf, (int, float, str, bool, type(None), np.ndarray, np.floating, np.integer)):
                    bad.append(f"agent {i}: non-data leaf at {path}: {type(leaf).__name__}")
                if isinstance(leaf, np.ndarray) and leaf.flags.writeable:
                    bad.append(f"agent {i}: writeable array at {path}")
        return bad

    # ----- oracle-only diagnostics -------------------------------------------
    def _oracle(self, name: str):
        if self.mode != "oracle":
            raise PermissionError(f"{name} is an oracle diagnostic; env mode is {self.mode!r}")
        self.access_log[name] += 1

    def oracle_payloads(self, i: int) -> Dict[int, MessagePayload]:
        """ORACLE: fresh summaries of all neighbours of i, not charged, not delivered."""
        self._oracle("oracle_payloads")
        return {j: decode_payload(encode_payload(self._summary(j))[0]) for j in self.neighbours[int(i)]}

    def counterfactual_view(self, i: int, heard: Sequence[int]) -> AgentView:
        """ORACLE: the view i WOULD have after hearing exactly `heard` fresh now (delay 0).

        Nothing is charged or cached.  Used to evaluate Q(s, S) for every S on a frozen critic.
        """
        self._oracle("counterfactual_view")
        if self._stage not in ("revise", "transmit"):
            raise RuntimeError("counterfactual views are defined after the reveal and before transmission")
        heard = tuple(int(j) for j in heard)
        if not set(heard) <= set(self.neighbours[int(i)]):
            raise ValueError("heard set must be neighbours")
        override = {j: decode_payload(encode_payload(self._summary(j))[0]) for j in heard}
        return self._build_view(int(i), inbox_override=override)

    def _snapshot(self):
        py = {k: copy.deepcopy(v) for k, v in self.__dict__.items() if k not in ("_engine", "access_log")}
        return (self._engine.snapshot(), py)

    def _restore(self, state):
        archive, py = state
        self._engine.load(archive)
        for k, v in py.items():
            setattr(self, k, copy.deepcopy(v))
        for i, iid in enumerate(self.agent_ids):
            self._engine.set_tl_phase(iid, int(self._phase[i]))

    def clone_state(self):
        """ORACLE: full simulator + protocol state (for rollout estimates)."""
        self._oracle("clone_state")
        return self._snapshot()

    def restore_state(self, state):
        if self.mode != "oracle":
            raise PermissionError("restore_state is oracle-only")
        self._restore(state)

    def oracle_rollout_value(self, joint_actions: Mapping[int, int], horizon_decisions: int = 3) -> float:
        """ORACLE: team value of `joint_actions` now, then hold phases, over the horizon.

        Value = - sum over the horizon's decision boundaries of total waiting vehicles on
        controlled incoming lanes.  Clone/restore: the env state is unchanged afterwards.
        """
        self._oracle("oracle_rollout")
        state = self._snapshot()
        try:
            total = 0.0
            for i, iid in enumerate(self.agent_ids):
                a = int(joint_actions[i])
                if a not in self._topology[i].valid_phases:
                    raise ValueError("invalid phase in rollout")
                self._engine.set_tl_phase(iid, a)
            for _ in range(int(horizon_decisions)):
                for _ in range(self.action_interval):
                    self._engine.next_step()
                self._read_lanes()
                total -= self._total_waiting()
            return total
        finally:
            self._restore(state)


# ---------------------------------------------------------------------------
# Driver helper: one protocol step with wall-clock selector latency
# ---------------------------------------------------------------------------

def run_protocol_step(env: BudgetedCityFlowEnv, policy, *, audit: bool = True):
    """policy: rank(view, topo) -> ranking; revise(view, ranking, k, R) -> set; act(view, topo) -> phase."""
    violations = []
    topo = {i: env.public_topology(i) for i in range(env.n_agents)}
    views = env.views()
    if audit:
        violations += env.check_access_invariants(views)
    t0 = time.perf_counter()
    rankings = {i: tuple(policy.rank(views[i], topo[i])) for i in views}
    t1 = time.perf_counter()
    env.commit_rankings(rankings)
    k = env.reveal_budget()
    views = env.views()
    if audit:
        violations += env.check_access_invariants(views)
    t2 = time.perf_counter()
    finals = {i: tuple(policy.revise(views[i], rankings[i], k[i], env.R)) for i in views}
    t3 = time.perf_counter()
    env.submit_final_sets(finals)
    views = env.transmit()
    if audit:
        violations += env.check_access_invariants(views)
    t4 = time.perf_counter()
    actions = {i: int(policy.act(views[i], topo[i])) for i in views}
    t5 = time.perf_counter()
    rewards, done, rec = env.step(actions)
    rec = dict(rec)
    rec["selector_seconds"] = (t1 - t0) + (t3 - t2)
    rec["actor_seconds"] = t5 - t4
    rec["violations"] = violations
    return rewards, done, rec


# ---------------------------------------------------------------------------
# Scenario builder and factory (isolated runtime only)
# ---------------------------------------------------------------------------

def _cityflow_generator_dir() -> Path:
    from envs.external.runtime import external_root
    return external_root() / "repos" / "CityFlow" / "tools" / "generator"


def _load_generator():
    gdir = _cityflow_generator_dir()
    import sys
    if str(gdir) not in sys.path:
        sys.path.insert(0, str(gdir))
    spec = importlib.util.spec_from_file_location("cf_generate_json_from_grid", gdir / "generate_json_from_grid.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    spec2 = importlib.util.spec_from_file_location("cf_generate_grid_scenario", gdir / "generate_grid_scenario.py")
    mod2 = importlib.util.module_from_spec(spec2)
    spec2.loader.exec_module(mod2)
    return mod.gridToRoadnet, mod2.generate_route


VEHICLE_TEMPLATE = {"length": 5.0, "width": 2.0, "maxPosAcc": 2.0, "maxNegAcc": 4.5, "usualPosAcc": 2.0,
                    "usualNegAcc": 4.5, "minGap": 2.5, "maxSpeed": 16.67, "headwayTime": 1.5}


def make_grid_scenario(out_dir: Path, rows: int, cols: int, traffic_seed: int, horizon_s: int,
                       mean_headway_s: float = 12.0, turn: bool = True) -> dict:
    """Write roadnet/flow/config for a rows x cols grid with seeded Poisson arrivals.

    The roadnet comes from the pinned CityFlow generator (imported read-only).  Each route
    gets arrivals with exponential headways (mean `mean_headway_s`) drawn from `traffic_seed`;
    each vehicle is a one-vehicle flow (startTime = endTime).  Refuses to overwrite.
    """
    out_dir = Path(out_dir)
    if out_dir.exists():
        raise FileExistsError(f"refusing to overwrite scenario dir {out_dir}")
    out_dir.mkdir(parents=True)
    gridToRoadnet, generate_route = _load_generator()
    roadnet = gridToRoadnet(rowNumber=rows, columnNumber=cols, rowDistances=[300] * (cols - 1),
                            columnDistances=[300] * (rows - 1), outRowDistance=300, outColumnDistance=300,
                            intersectionWidths=[[30] * cols] * rows, numLeftLanes=1, numStraightLanes=1,
                            numRightLanes=1, laneMaxSpeed=16.67, tlPlan=False)
    rng = np.random.default_rng([int(traffic_seed), 0xF10])
    flows = []
    for route in generate_route(rows, cols, turn):
        t = float(rng.exponential(mean_headway_s))
        while t < horizon_s:
            ts = int(t)
            flows.append({"vehicle": dict(VEHICLE_TEMPLATE), "route": list(route), "interval": 1.0,
                          "startTime": ts, "endTime": ts})
            t += float(rng.exponential(mean_headway_s))
    config = {"interval": 1.0, "seed": int(traffic_seed), "dir": str(out_dir) + os.sep,
              "roadnetFile": "roadnet.json", "flowFile": "flow.json", "rlTrafficLight": True,
              "laneChange": False, "saveReplay": False}
    paths = {}
    for name, obj in (("roadnet.json", roadnet), ("flow.json", flows), ("config.json", config)):
        p = out_dir / name
        p.write_text(json.dumps(obj), encoding="utf-8")
        paths[name] = {"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
    return {"dir": str(out_dir), "files": paths, "n_vehicles": len(flows), "rows": rows, "cols": cols,
            "traffic_seed": int(traffic_seed), "horizon_s": int(horizon_s), "mean_headway_s": mean_headway_s,
            "turn": bool(turn)}


def make_budgeted_grid_env(scenario: dict, *, budget_spec: BudgetTraceSpec, R: Optional[int], n_decisions: int,
                           action_interval: int = 10, delivery_delay: int = 0, mode: str = "deploy"):
    """Construct the env on a scenario from make_grid_scenario.  Isolated runtime only."""
    if os.environ.get("CIG_EXTERNAL_RUNTIME_ACTIVE") != "1":
        raise RuntimeError("CityFlow construction attempted outside the managed external runtime "
                           "(set by envs.external.runtime.maybe_reexec_in_external_runtime)")
    import cityflow
    cfg = scenario["files"]["config.json"]["path"]
    engine = cityflow.Engine(cfg, thread_num=1)
    roadnet = json.loads(Path(scenario["files"]["roadnet.json"]["path"]).read_text(encoding="utf-8"))
    return BudgetedCityFlowEnv(engine, roadnet, budget_spec=budget_spec, R=R, n_decisions=n_decisions,
                               action_interval=action_interval, delivery_delay=delivery_delay, mode=mode)
