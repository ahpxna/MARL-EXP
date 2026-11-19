#!/usr/bin/env python3
"""Midtown transfer wrapper (10/10/2026; user: "cho chạy trên map nyc manhattan thật ... map gốc ko bị cắt"; "lấy cái config tối ưu nhất
này cho chạy trên map đó thì còn tối ưu ko?").  Runs any grid4 evaluator chain UNCHANGED on the full OSM Midtown Manhattan network
(research/city_sim/net/midtown.net.xml, 248 signals, netconvert-guessed static programs) by re-pointing the network and demand constants
of CITY_q7_cross_version, which every evaluator reads at call time:
  Q7.NET_S -> midtown.net.xml, Q7.NET_A -> midtown_actuated.net.xml, Q7.ROU -> demand/midtown_$MT_DEMAND_s{seed}.rou.xml (default p075 =
  4 800 veh/h, randomTrips fringe-factor 5, min-distance 400 m).
Nothing is retrained.  The light and fleet checkpoints are the grid4 ones.  The only change is the SPaT forecast, whose N2 model was fitted
with a one-hot identity over the 16 grid4 lights and whose c2 table is keyed by grid4 light IDs:
  (1) identity: a Midtown light gets the AVERAGE grid4 identity (1/16 in every slot); every state feature is computed as on grid4;
  (2) yellow branch (hyb): the c2 table is rebuilt on the Midtown programs (greens = CITY_env.NetInfo's first two greens, the ones the
      light controller switches; non-green time between them = the program's durations, which include any third green, run at its static
      time because LightRL makes no decision there), with the grid4 table's POOLED green-duration samples (no per-light samples).
make_spat_n4_mt below is CITY_spat_forecast_n4.make_spat_n4 (sha256 recorded in MT_N4_SRC) with only those two changes, marked "MT".
Usage: DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py [scripts/DEMO_record.py] scripts/CITY_eval_n4.py ..."""
import hashlib, json, os, runpy, sys
from pathlib import Path
import numpy as np
import sumolib
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_forecast_n4 as N4  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402

NET = ROOT / 'research/city_sim/net'; DEM = os.environ.get('MT_DEMAND', 'p075')
# MT-C (11/10 06:2x): MT_NET picks the network: 'midtown' (default, the 02/10 extract) or 'midtown_full' (the full Overpass extract of 11/10);
# its actuated twin and its demand files follow the same name.
MTN = os.environ.get('MT_NET', 'midtown'); assert MTN in ('midtown', 'midtown_full'), MTN
Q7.NET_S = str(NET / f'{MTN}.net.xml'); Q7.NET_A = str(NET / f'{MTN}_actuated.net.xml')
Q7.ROU = str(ROOT / f'research/city_sim/demand/{MTN}_{DEM}_s{{}}.rou.xml')
# training traffic for any trainer run through this wrapper: Midtown seeds 10-17 (same randomTrips command), disjoint from the test seeds 0-2
Q7.TRAIN_SEEDS = [int(x) for x in os.environ.get('MT_TRAIN_SEEDS', '10,11,12,13,14,15,16,17').split(',')]
MT_N4_SRC = hashlib.sha256(Path(N4.__file__).read_bytes()).hexdigest()
# Amendment MT-A1 (10/10 23:0x, after the smoke, before any full run): the learned light was trained on two-green lights only.  On the
# Midtown lights with three greens (avenue, protected left, cross street) NetInfo's first two greens both serve the avenue, the cross
# street is never observed, and the light starves it (smoke: every RL-caused teleport sat at such a light).  With MT_TWO_GREEN=1 (default)
# NetInfo keeps only the lights whose program has exactly two greens (224 of 248); the 10 three-green and 14 one-green lights keep their
# static program, the forecast answers 'unavailable' there (the fleet drives sigma*), as for any light outside the provider's support.
MT_TWO_GREEN = os.environ.get('MT_TWO_GREEN', '1') == '1'; _ni_init = CE.NetInfo.__init__


def _ni_two_green(self, net_file):
    _ni_init(self, net_file)
    if MT_TWO_GREEN and Path(net_file).name.startswith('midtown'):
        for t in sumolib.net.readNet(net_file, withPrograms=True).getTrafficLights():
            ph = list(t.getPrograms().values())[0].getPhases()
            if sum(('G' in p.state or 'g' in p.state) and 'y' not in p.state.lower() for p in ph) != 2:
                self.tls.pop(t.getID(), None)


CE.NetInfo.__init__ = _ni_two_green
# Amendment MT-A2 (10/10 23:1x, user: "Today ... có bám sát với thực tế ko? ... dùng config giống với thực tế hơn ko?"): MT_BASE=nyc loads the
# NYC-like fixed-time plan (scripts/MT_nyc_timing.py: 90 s cycles, Webster splits and green-wave offsets tuned on TRAINING traffic seed 10,
# original yellows / phase structure) as the active program of every signal, for every arm except ACT (its own actuated net).  Under a learned
# light it is the plan of the lights the AI does not control.  MT_BASE=osm (default) keeps netconvert's plan (90 s, even splits, offset 0).
# Amendment MT-A4 (11/10 01:1x): MT_TTT=<seconds> replaces SUMO's --time-to-teleport (300 in CITY_env.run_episode) in every simulation
# this process starts; MT_TTT=-1 disables teleports.  Used ONLY for light training: the MT-A3 lights starved approaches until SUMO
# removed the stuck cars (164 of 207 test teleports on day 0 at the lights they control), which also removed those cars from the reward.
if os.environ.get('MT_TTT'):
    _ls_start = CE.ls.start

    def _start_ttt(cmd, *a, **k):
        cmd = list(cmd); i = cmd.index('--time-to-teleport'); cmd[i + 1] = os.environ['MT_TTT']; return _ls_start(cmd, *a, **k)
    CE.ls.start = _start_ttt
# Amendment MT-A6 (11/10 02:5x): the open-loop / closed-loop forecast tables (CITY_spat_forecast.fit, used by the W19 forecaster pipeline,
# CITY_m3_train_E.prep and CITY_n2_fit) are fitted only on the lights NetInfo knows (the AI-controlled two-green lights); recorded traces
# also carry the other Midtown signals, which the original fit cannot look up.  Identical to the original whenever every id is known (grid).
import scripts.CITY_spat_forecast as FC  # noqa: E402


def _greens_known(ids):
    info = CE.NetInfo(Q7.NET_S); return {t: list(info.tls[t]['greens']) for t in ids if t in info.tls}


def _fit_known(files):
    T, G = {}, {}
    for f in files:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P = z['phases']; G = _greens_known(ids)
        for j, tid in enumerate(ids):
            if tid not in G:
                continue
            for ph, _st, ln, complete in FC.runs(P[:, j]):
                if complete and ph in G[tid]:
                    T.setdefault(tid, {}).setdefault(str(ph), []).append(ln)
    pooled = {}
    for tid in T:
        for g, v in T[tid].items():
            pooled.setdefault(str(G[tid].index(int(g))), []).extend(v)
    return dict(per=T, pooled=pooled, greens=G, n_files=len(files))


FC.greens_of, FC.fit = _greens_known, _fit_known
# Amendment MT-A5 (11/10 02:0x): MT_LIGHT_INDEX=1 appends the light's index (position in sorted NetInfo ids) to every light observation,
# for the per-light (local) networks of scripts/CITY_mt_train_light_moe.py, in training and evaluation alike.  Wrapped per instance at
# LightRL.__init__, so the class-level family / adapter patches made later (W19 family_obs, CITY_eval4.LightRLX) still run first.
if os.environ.get('MT_LIGHT_INDEX') == '1':
    _lr_init = CE.LightRL.__init__

    def _lr_init_idx(self, info, *a, **k):
        _lr_init(self, info, *a, **k)
        idx = {t: float(i) for i, t in enumerate(sorted(info.tls))}

        def obs_idx(tid, _self=self):
            o, h, c = type(_self).obs(_self, tid)
            return np.append(o, idx[tid]).astype(np.float32), h, c
        self.obs = obs_idx
    CE.LightRL.__init__ = _lr_init_idx
# Amendment MT-D (11/10 06:4x): MT_MAX_G=<seconds> gives every learned light a maximum green (forced switch, CITY_env.LightRL's max_g, the
# Q7 "compatible mode" RL-C50).  50 s = maxDur of the actuated programs netconvert builds for these nets (1 152 of 1 154 phases on the full net).
if os.environ.get('MT_MAX_G'):
    import scripts.CITY_eval4 as _E4m
    _lx_init = _E4m.LightRLX.__init__

    def _lx_init_maxg(self, info, policy, max_g=None, adapter='raw', box=None):
        _lx_init(self, info, policy, max_g=float(os.environ['MT_MAX_G']), adapter=adapter, box=box)
    _E4m.LightRLX.__init__ = _lx_init_maxg
MT_BASE = os.environ.get('MT_BASE', 'osm'); NYC_ADD = ROOT / 'research/city_sim/midtown_transfer_20261010/nyc_timing/nyc.add.xml'
# Amendment MT-E (11/10 06:5x): MT_BASE=actrest (full map only) runs the signals the AI does NOT control (56 of 567: one-green and 3- to 7-green
# junctions) on the actuated programs of midtown_full_actuated.net.xml (identical link indices, checked) instead of the static plan.
if MT_BASE == 'actrest':
    assert MTN == 'midtown_full', 'MT_BASE=actrest needs MT_NET=midtown_full'; NYC_ADD = NET / 'midtown_full_act_rest.add.xml'
if MT_BASE in ('nyc', 'actrest'):
    import scripts.CITY_eval4 as _E4
    _bl = _E4.build_light

    def build_light_nyc(spec, info, adapter, box):
        net, light, extra, init = _bl(spec, info, adapter, box)
        return (net, light, list(extra), init) if spec.startswith('ACT') else (net, light, list(extra) + ['-a', str(NYC_ADD)], init)
    _E4.build_light = build_light_nyc
elif MT_BASE != 'osm':
    raise SystemExit(f'MT_BASE {MT_BASE}?')  # osm | nyc | actrest


def midtown_c2_table(prov):
    """c2-format table on the Midtown programs: NetInfo greens, program non-green durations, grid4 pooled samples, no per-light samples."""
    info = CE.NetInfo(Q7.NET_S); net = sumolib.net.readNet(Q7.NET_S, withPrograms=True); G, NG, NP, DUR = {}, {}, {}, {}
    for t in net.getTrafficLights():
        if t.getID() in info.tls:
            ph = list(t.getPrograms().values())[0].getPhases(); d = info.tls[t.getID()]; dur = [float(p.duration) for p in ph]
            G[t.getID()] = list(d['greens']); NP[t.getID()] = d['n_phases']; DUR[t.getID()] = dur; NG[t.getID()] = FK.ng_of(d['greens'], d['n_phases'], dur)
    # per-light samples are kept for the Midtown lights present (a provenance recorded on Midtown); a grid provenance has none of these ids,
    # so for it this is exactly the pooled-only table used before (MT-A6, 11/10 02:5x)
    per = {t: v for t, v in prov.get('per', {}).items() if t in G}
    return dict(per=per, pooled=prov['pooled'], greens=G, ng=NG, n_phases=NP, dur=DUR, kind='c2-midtown')


def make_spat_n4_mt(model_path, q, info, tracker, gate):
    d = torch.load(model_path, weights_only=False); net = N4.NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval(); qs = list(d['qs'])
    qi, i1, i5 = qs.index(q), qs.index(0.1), qs.index(0.5); ids = list(d['ids']); L = len(ids); cache = {}; st_cache = {}
    kind, _, par = gate.partition(':'); stats = dict(valid=0, published=0, hybrid=0, avg_identity=0)
    P = [float(x) for x in par.split(',')] if (par and kind != 'hyb') else []
    if kind == 'hyb':
        C2S = FK.make_spat_k(midtown_c2_table(json.load(open(par))), q)[0]          # MT (2): Midtown programs, grid4 pooled samples

    def feats(tid, t):
        ls = CE.ls; dd = info.tls[tid]; gs = list(dd['greens']); ph = ls.trafficlight.getPhase(tid); s = ls.trafficlight.getSpentDuration(tid)
        ci = max([k for k, g in enumerate(gs) if g <= ph], default=len(gs) - 1); cur = gs[ci]
        H = [sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in dd['serve'][:2]]; V = [sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in dd['serve'][:2]]
        oh = np.zeros(4, np.float32); oh[min(ph, 3)] = 1; rows, keys = [], []
        if tid in ids:
            eye = np.zeros(L, np.float32); eye[ids.index(tid)] = 1
        else:
            eye = np.full(L, 1.0 / L, np.float32); stats['avg_identity'] += 1                  # MT (1): average grid4 identity
        for gk, g in enumerate(gs):
            kd = 0 if ph == g else 1; ti = (1 - gk) if kd == 0 else gk
            rows.append(np.concatenate([oh, [s / 60.0, float(kd), H[ci] / 10.0, V[ci] / 20.0, H[ti] / 10.0, V[ti] / 20.0, tracker.mean(tid, cur, ph) / 60.0,
                                             tracker.mean(tid, g, ph) / 60.0], eye]).astype(np.float32)); keys.append((g, kd))
        with torch.no_grad():
            pr = net(torch.as_tensor(np.stack(rows))).numpy()
        return {k: (float(v[qi]), float(v[i5] - v[i1])) for k, v in zip(keys, pr)}, ph

    def ok(tid, link, t, green, val, w):
        if kind in ('all', 'hyb'):
            return True
        if kind == 'w':
            return w <= P[0]
        if kind == 'h':
            return green or val <= P[0]
        if kind == 'wh':
            return w <= P[0] and (green or val <= P[1])
        if kind == 'rnd':
            h = int(hashlib.sha256(f'{tid}|{link}|{int(t) // 5}'.encode()).hexdigest()[:8], 16) / 0xFFFFFFFF; return h < P[0]
        raise ValueError(gate)

    def spat(tid, link):
        if tid not in info.tls:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
        ls = CE.ls; t = ls.simulation.getTime()
        if tid not in st_cache:
            st_cache[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = st_cache[tid]; gs = list(info.tls[tid]['greens']); serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs):
            return dict(ttg=0.0, ttr=999.0, valid=True, source=f'n4:{q}')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        if kind == 'hyb' and ls.trafficlight.getPhase(tid) not in gs:
            stats['valid'] += 1; stats['published'] += 1; stats['hybrid'] += 1; return C2S(tid, link)
        if cache.get(tid, (None,))[0] != t:
            cache[tid] = (t,) + feats(tid, t)
        _, pred, ph = cache[tid]; stats['valid'] += 1
        if ph in serve:
            val, w = pred[(ph, 0)]; green = True
        else:
            g = min(serve, key=lambda g: pred[(g, 1)][0]); val, w = pred[(g, 1)]; green = False
        if not ok(tid, link, t, green, max(0.0, val), w):
            return dict(ttg=0.0, ttr=0.0, valid=False, source='gated')
        stats['published'] += 1
        return dict(ttg=0.0, ttr=max(0.0, val), valid=True, source=f'n4:{q}') if green else dict(ttg=max(0.0, val), ttr=0.0, valid=True, source=f'n4:{q}')
    spat.stats = stats
    return spat


N4.make_spat_n4 = make_spat_n4_mt
if os.environ.get('MT_TELE_LOG'):                       # diagnostic only: every teleport start with the vehicle's last lane and waiting time
    import scripts.CITY_eval4 as E4
    _rep = E4.run_episode

    def run_episode(net, rou, seed, light, cars, **kw):
        inner = light; last = {}; ev = []

        class Tele:
            def step(self, t):
                if inner is not None:
                    inner.step(t)
                ls = CE.ls
                for v in ls.simulation.getStartingTeleportIDList():
                    ln, w = last.get(v, ('?', -1.0))
                    ev.append(dict(t=int(t), v=v, lane=ln, wait=w, agent=bool(cars.is_agent(v)) if cars is not None else False))
                for v in ls.vehicle.getIDList():
                    ln = ls.vehicle.getLaneID(v)
                    if ln:
                        last[v] = (ln, ls.vehicle.getWaitingTime(v))
        out = _rep(net, rou, seed, Tele(), cars, **kw)
        Path(os.environ['MT_TELE_LOG']).write_text(json.dumps(ev)); print(f'MT teleports logged: {len(ev)}', flush=True)
        return out
    E4.run_episode = run_episode
print(f"MIDTOWN wrapper: net {Q7.NET_S}, demand {Q7.ROU}, n4 source {MT_N4_SRC[:12]}, two-green only {MT_TWO_GREEN}, base plan {MT_BASE}, light index {os.environ.get('MT_LIGHT_INDEX') == '1'}, max green {os.environ.get('MT_MAX_G', 'none')}", flush=True)
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
