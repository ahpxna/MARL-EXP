#!/usr/bin/env python3
"""Field data F2 inventory (FIELD_DATA_SURVEY_20261008): which VED vehicles carry a direct OBD fuel-rate signal, which only MAF.
Streams every weekly CSV out of the two 7z archives with bsdtar (nothing is extracted to disk) and reads the static vehicle table
(xlsx parsed as zipped XML; openpyxl is not installed).  Output: research/field_data/ved_inventory.json (per vehicle: type, engine,
weight, rows, rows with Fuel Rate, rows with MAF, rows with fuel trims, trips, km).  Usage: CITY python FIELD_ved_inventory.py"""
import html, io, json, re, subprocess, sys, zipfile
from pathlib import Path
import numpy as np
import pandas as pd
ROOT = Path(__file__).resolve().parents[1]; F = ROOT / 'research/field_data'; V = F / 'ved'


def xlsx_rows(path):
    z = zipfile.ZipFile(path); ss = []
    if 'xl/sharedStrings.xml' in z.namelist():
        x = z.read('xl/sharedStrings.xml').decode()
        ss = [html.unescape(re.sub(r'<[^>]+>', '', m)) for m in re.findall(r'<si>(.*?)</si>', x, re.S)]
    sheet = sorted(n for n in z.namelist() if n.startswith('xl/worksheets/sheet'))[0]; x = z.read(sheet).decode(); out = []
    for row in re.findall(r'<row[^>]*>(.*?)</row>', x, re.S):
        cells = {}
        for ref, attrs, body in re.findall(r'<c r="([A-Z]+)\d+"([^>]*)>(.*?)</c>', row, re.S):
            v = re.search(r'<v>(.*?)</v>', body); v = v.group(1) if v else ''
            if 't="s"' in attrs and v != '':
                v = ss[int(v)]
            cells[ref] = v
        out.append(cells)
    hdr = out[0]; cols = sorted(hdr, key=lambda c: (len(c), c))
    return [{hdr[c]: r.get(c, '') for c in cols} for r in out[1:]]


static = {}
for p in sorted(V.glob('VED_Static_Data_*.xlsx')):
    for r in xlsx_rows(p):
        if r.get('VehId'):
            static[int(float(r['VehId']))] = r
acc = {}
for arc in sorted(V.glob('VED_DynamicData_Part*.7z')):
    names = [l.split()[-1] for l in subprocess.run(['bsdtar', '-tvf', str(arc)], capture_output=True, text=True).stdout.splitlines()]
    for nm in names:
        pr = subprocess.Popen(['bsdtar', '-xOf', str(arc), nm], stdout=subprocess.PIPE)
        for ch in pd.read_csv(pr.stdout, chunksize=500_000, low_memory=False):
            ch = ch.sort_values(['VehId', 'Trip', 'Timestamp(ms)'])
            dt = ch.groupby(['VehId', 'Trip'])['Timestamp(ms)'].diff().fillna(0).clip(0, 5000) / 1000.0
            km = ch['Vehicle Speed[km/h]'].fillna(0) * dt / 3600.0
            g = pd.DataFrame(dict(VehId=ch['VehId'], Trip=ch['Trip'], fr=ch['Fuel Rate[L/hr]'].notna(), maf=ch['MAF[g/sec]'].notna(),
                                  trim=ch['Short Term Fuel Trim Bank 1[%]'].notna(), km=km))
            for vid, d in g.groupby('VehId'):
                a = acc.setdefault(int(vid), dict(rows=0, fuel_rate=0, maf=0, trim=0, km=0.0, trips=set()))
                a['rows'] += len(d); a['fuel_rate'] += int(d.fr.sum()); a['maf'] += int(d.maf.sum()); a['trim'] += int(d.trim.sum())
                a['km'] += float(d.km.sum()); a['trips'].update(int(t) for t in d.Trip.unique())
        pr.wait(); print('done', nm, len(acc), flush=True)
out = {}
for vid, a in sorted(acc.items()):
    s = static.get(vid, {})
    out[vid] = dict(type=s.get('Vehicle Type', s.get('EngineType', '')), engine=s.get('Engine Configuration & Displacement', ''), weight=s.get('Generalized_Weight', ''),
                    transmission=s.get('Transmission', ''), rows=a['rows'], fuel_rate=a['fuel_rate'], maf=a['maf'], trim=a['trim'],
                    km=round(a['km'], 1), trips=len(a['trips']))
(F / 'ved_inventory.json').write_text(json.dumps(out, indent=1))
ice = {k: v for k, v in out.items() if v['type'] == 'ICE'}
fr = {k: v for k, v in ice.items() if v['fuel_rate'] > 0.5 * v['rows']}
print(f'vehicles {len(out)}; ICE {len(ice)}; ICE with Fuel Rate on >50% rows {len(fr)} '
      f'({sum(v["km"] for v in fr.values()):.0f} km); ICE with MAF on >50% rows {sum(1 for v in ice.values() if v["maf"] > 0.5 * v["rows"])}')
