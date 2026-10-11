#!/usr/bin/env python3
"""Live SUMO viewer for the city-sim track (02/10/2026 17:4x).  sumo-gui needs an X11 server (XQuartz), which this Mac does
not have, so this script runs the simulation itself (libsumo, one background thread) and streams every step to a canvas
page over server-sent events: vehicles (position, heading, speed, agent or not) and every signal head (state of the links
leaving each controlled lane).  The page interpolates between steps, zooms with the wheel and pans by dragging.
Controllers are pluggable through CITY_env.make_controllers (signals: 'fixed' = the net's own programs; vehicles: 'default'
= the routes in the route file); without CITY_env only the fixed / default pair is available.
Usage: CITY_live_viewer.py --net NET --routes ROU [--port 8770] [--end 3600] [--seed 0] [--signals fixed] [--vehicles default]"""
from __future__ import annotations
import argparse, json, math, sys, threading, time
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlparse, parse_qs

import libsumo as ls
import sumolib
import traci.constants as tc

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
RANK = {'G': 4, 'g': 3, 'y': 2, 'Y': 2, 'u': 1, 'o': 1, 'O': 1, 'r': 0, 's': 0}


def net_geometry(net_file):
    """Lane polylines, junction polygons and one signal head per controlled incoming lane (net coordinates, metres)."""
    net = sumolib.net.readNet(net_file, withInternal=False, withPrograms=True)
    lanes = [dict(s=[[round(x, 1), round(y, 1)] for x, y in ln.getShape()], w=round(ln.getWidth(), 2))
             for e in net.getEdges() if e.getFunction() != 'internal' for ln in e.getLanes()]
    junctions = [[[round(x, 1), round(y, 1)] for x, y in n.getShape()] for n in net.getNodes() if len(n.getShape()) >= 3]
    names = []
    for e in net.getEdges():
        nm = e.getName()
        if nm and e.getLength() > 120:
            sh = e.getShape(); (x0, y0), (x1, y1) = sh[0], sh[-1]
            names.append(dict(n=nm, x=round((x0 + x1) / 2, 1), y=round((y0 + y1) / 2, 1), a=round(math.atan2(y1 - y0, x1 - x0), 3)))
    heads, head_links = [], []          # one head per (tls, incoming lane); head_links[k] = (tls id, [link indices])
    for t in net.getTrafficLights():
        by_lane = {}
        for in_lane, _out, idx in t.getConnections():
            by_lane.setdefault(in_lane.getID(), (in_lane, []))[1].append(idx)
        for lid, (ln, idxs) in by_lane.items():
            sh = ln.getShape(); (x0, y0), (x1, y1) = sh[-2], sh[-1]; a = math.atan2(y1 - y0, x1 - x0)
            heads.append(dict(x=round(x1 - 1.5 * math.cos(a), 1), y=round(y1 - 1.5 * math.sin(a), 1), a=round(a, 3), w=round(ln.getWidth(), 2)))
            head_links.append((t.getID(), sorted(idxs)))
    (xmin, ymin, xmax, ymax) = net.getBoundary()
    return dict(lanes=lanes, junctions=junctions, names=names, heads=heads, bounds=[xmin, ymin, xmax, ymax]), head_links


class Sim(threading.Thread):
    def __init__(self, a, head_links):
        super().__init__(daemon=True)
        self.a, self.head_links = a, head_links
        self.cond = threading.Condition(); self.frame, self.seq = None, 0
        self.speed, self.paused, self.restart = 1.0, False, False
        self.ids, self.next_id = {}, 0

    def start_sumo(self):
        cmd = [sumolib.checkBinary('sumo'), '-n', self.a.net, '-r', self.a.routes, '--seed', str(self.a.seed), '--no-step-log',
               '--no-warnings', '--time-to-teleport', '300', '--step-length', '1']
        ls.start(cmd)
        self.ctrl = []
        if self.a.signals != 'fixed' or self.a.vehicles != 'default':
            from scripts.CITY_env import make_controllers  # RL controllers live with the environment
            self.ctrl = make_controllers(ls, self.a.net, self.a.signals, self.a.vehicles, self.a.seed)
        self.arrived = self.teleports = 0; self.ids.clear(); self.next_id = 0

    def snapshot(self):
        for v in ls.simulation.getDepartedIDList():
            ls.vehicle.subscribe(v, [tc.VAR_POSITION, tc.VAR_ANGLE, tc.VAR_SPEED, tc.VAR_TYPE])
        sub = ls.vehicle.getAllSubscriptionResults(); veh = []; halting = 0; sp = 0.0
        for v, r in sub.items():
            if v not in self.ids:
                self.ids[v] = self.next_id; self.next_id += 1
            (x, y), s = r[tc.VAR_POSITION], r[tc.VAR_SPEED]
            halting += s < 0.1; sp += s
            veh.append([self.ids[v], round(x, 1), round(y, 1), round(r[tc.VAR_ANGLE], 1), round(s, 1), 1 if r[tc.VAR_TYPE].startswith('cav') else 0])
        states = {}
        sig = []
        for tid, idxs in self.head_links:
            st = states.get(tid) or states.setdefault(tid, ls.trafficlight.getRedYellowGreenState(tid))
            sig.append(max((st[i] for i in idxs if i < len(st)), key=lambda c: RANK.get(c, 0), default='r'))
        self.arrived += ls.simulation.getArrivedNumber(); self.teleports += ls.simulation.getStartingTeleportNumber()
        info = dict(t=ls.simulation.getTime(), running=len(veh), arrived=self.arrived, halting=halting,
                    mean_speed=round(sp / max(1, len(veh)), 2), teleports=self.teleports, speed=self.speed, paused=self.paused,
                    signals=self.a.signals, vehicles=self.a.vehicles)
        return json.dumps(dict(v=veh, s=''.join(sig), i=info), separators=(',', ':'))

    def run(self):
        while True:
            self.start_sumo(); self.restart = False
            self.publish(self.snapshot())
            while ls.simulation.getTime() < self.a.end and not self.restart:
                if self.paused:
                    time.sleep(0.05); continue
                t0 = time.time()
                ls.simulationStep()
                for c in self.ctrl:
                    c.step()
                self.publish(self.snapshot())
                time.sleep(max(0.0, 1.0 / max(self.speed, 1e-3) - (time.time() - t0)))
            ls.close()
            if not self.restart:                     # finished: hold the last frame until a restart is requested
                while not self.restart:
                    time.sleep(0.1)

    def publish(self, frame):
        with self.cond:
            self.frame, self.seq = frame, self.seq + 1; self.cond.notify_all()


PAGE = (ROOT / 'scripts' / 'CITY_live_viewer.html')


def serve(a):
    geo, head_links = net_geometry(a.net); geo_json = json.dumps(geo, separators=(',', ':'))
    sim = Sim(a, head_links); sim.start()

    class H(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def send(self, code, body, ctype):
            b = body.encode() if isinstance(body, str) else body
            self.send_response(code); self.send_header('Content-Type', ctype); self.send_header('Content-Length', str(len(b)))
            self.send_header('Cache-Control', 'no-store'); self.end_headers(); self.wfile.write(b)

        def do_GET(self):
            u = urlparse(self.path); q = parse_qs(u.query)
            if u.path == '/':
                return self.send(200, PAGE.read_text(), 'text/html; charset=utf-8')
            if u.path == '/net.json':
                return self.send(200, geo_json, 'application/json')
            if u.path == '/control':
                if 'speed' in q:
                    sim.speed = min(200.0, max(0.25, float(q['speed'][0])))
                if 'pause' in q:
                    sim.paused = q['pause'][0] == '1'
                if 'restart' in q:
                    sim.restart = True; sim.paused = False
                return self.send(200, json.dumps(dict(speed=sim.speed, paused=sim.paused)), 'application/json')
            if u.path == '/events':
                self.send_response(200); self.send_header('Content-Type', 'text/event-stream'); self.send_header('Cache-Control', 'no-store')
                self.end_headers(); last = 0
                try:
                    while True:
                        with sim.cond:
                            sim.cond.wait_for(lambda: sim.seq != last, timeout=15)
                            frame, last = sim.frame, sim.seq
                        self.wfile.write(b'data: ' + (frame or '{}').encode() + b'\n\n'); self.wfile.flush()
                except (BrokenPipeError, ConnectionResetError):
                    return
            return self.send(404, 'not found', 'text/plain')

    print(f'CITY live viewer on http://localhost:{a.port}  net={a.net} routes={a.routes} signals={a.signals} vehicles={a.vehicles}', flush=True)
    ThreadingHTTPServer(('127.0.0.1', a.port), H).serve_forever()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--net', required=True); ap.add_argument('--routes', required=True)
    ap.add_argument('--port', type=int, default=8770); ap.add_argument('--end', type=float, default=3600); ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--signals', default='fixed'); ap.add_argument('--vehicles', default='default')
    serve(ap.parse_args())
