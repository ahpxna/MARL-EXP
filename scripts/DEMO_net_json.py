#!/usr/bin/env python3
"""Demo: map geometry for the browser replay (10/10/2026).  Reads a SUMO net and writes {lanes, tls, junctions, bbox}:
  lanes      every non-internal lane's shape, [[x, y], ...] in metres (0.1 m)
  tls        {tls id: [[link index, stop-line x, y, previous shape point x, y], ...]} (the page draws a bar across the lane end)
  junctions  centre of every signal-controlled junction
  bbox       the net's convBoundary
Usage: DEMO_net_json.py <net.xml> <out.json>"""
import json, sys
import sumolib

r = lambda v: round(float(v), 1)
net = sumolib.net.readNet(sys.argv[1], withPrograms=True, withInternal=False)
lanes = [[[r(x), r(y)] for x, y in ln.getShape()] for e in net.getEdges() if not e.isSpecial() for ln in e.getLanes()]
tls = {}
for t in net.getTrafficLights():
    seen = {}
    for a, _b, idx in t.getConnections():
        if idx not in seen:
            sh = a.getShape(); seen[idx] = [idx, r(sh[-1][0]), r(sh[-1][1]), r(sh[-2][0]), r(sh[-2][1])]
    tls[t.getID()] = [seen[k] for k in sorted(seen)]
jn = sorted({(r(n.getCoord()[0]), r(n.getCoord()[1])) for t in net.getTrafficLights() for n in t.getNodes()} if hasattr(sumolib.net.TLS, 'getNodes') else
            {(r(n.getCoord()[0]), r(n.getCoord()[1])) for n in net.getNodes() if n.getType() == 'traffic_light'})
x0, y0, x1, y1 = net.getBoundary()
json.dump(dict(lanes=lanes, tls=tls, junctions=[list(p) for p in jn], bbox=[r(x0), r(y0), r(x1), r(y1)]), open(sys.argv[2], 'w'), separators=(',', ':'))
print(sys.argv[2], len(lanes), 'lanes', len(tls), 'signals', len(jn), 'junctions')
