#!/usr/bin/env python3
"""W7-2 DCA2 evaluator (PROTOCOL_CITY_WAVE7_20261005): CITY_eval_n4.py (UNCHANGED, imported; TSI hybrid fleet service via --n4) with
  * env DCA2_PARAMS=<file.pt>: every signal controller's RL-H inputs pass through its OWN DC-Ada transformation layer (residual MLP
    7 -> 32 ReLU LayerNorm -> 32 ReLU -> 7, output + input; github.com/alqithami/DC-ADA src/agents/transformation.py), parameters
    {controller id: flat vector} from the file;
  * env DCA2_END=<seconds>: the episode is truncated at that horizon (DC-Ada's truncated candidate rollouts); default: the evaluator's own.
Usage (as CITY_eval_n4.py): CITY_eval_dca2.py --n4 0.5:hyb:<table>:<model> --light RL-H:k --fleet ... --seeds ... --tag T --out D"""
import os, sys
from pathlib import Path
import numpy as np
import torch
import torch.nn as nn
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval_n4 as N4  # noqa: E402
E4 = N4.E4; E4.SRC = f"{E4.SRC}+dca2:{N4.sha(Path(__file__).read_bytes())}"


from scripts.CITY_dcada_layer import TransformationLayer, NPARAM  # noqa: E402,F401



class LightDCA(E4.LightRLX):
    def __init__(self, info, policy, params):
        super().__init__(info, policy, adapter='raw'); self.T = {}
        for tid in info.tls:
            T = TransformationLayer(); T.set_params_vector(torch.as_tensor(params[tid], dtype=torch.float32)); T.eval(); self.T[tid] = T

    def obs(self, tid):
        o, halt, cur = super().obs(tid)
        with torch.no_grad():
            o2 = self.T[tid](torch.as_tensor(np.asarray(o, np.float32))[None])[0].numpy()
        return o2.astype(np.float32), halt, cur


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    net, L, a, b = _bl(spec, info, adapter, box)
    if os.environ.get('DCA2_PARAMS') and isinstance(L, E4.LightRLX):
        P = torch.load(os.environ['DCA2_PARAMS'], weights_only=False); assert set(P) == set(info.tls), 'controller ids'
        L = LightDCA(info, L.inner, P)
    return net, L, a, b


E4.build_light = build_light
_run = E4.run


def run(a, seed, end):
    return _run(a, seed, float(os.environ['DCA2_END']) if os.environ.get('DCA2_END') else end)


E4.run = run
if __name__ == '__main__':
    import json, hashlib
    sha = lambda b: hashlib.sha256(b).hexdigest()
    p = N4.argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(N4.REST)
    prior = Path(a.out, f'{a.tag}.json')
    if prior.exists() and json.loads(prior.read_text()).get('status') == 'COMPLETE':
        print('skip complete run', a.tag); raise SystemExit(0)
    meta = dict(N4.EF.META)
    if N4.gate.startswith('hyb:'):
        tp = N4.gate.split(':', 1)[1]; meta.update(table=tp, table_sha256=sha(Path(tp).read_bytes()))
    if a.fleet.startswith('PL:'):
        meta['fleet_sha256'] = sha(Path(a.fleet[3:]).read_bytes())
    if a.light.startswith('RL-H:'):
        from scripts.CITY_xplay2 import light_spec
        _n, ck, _x = light_spec(a.light); meta.update(light_checkpoint=str(ck), light_sha256=sha(Path(ck).read_bytes()))
    if os.environ.get('DCA2_PARAMS'):
        meta.update(dca2_params=os.environ['DCA2_PARAMS'], dca2_params_sha256=sha(Path(os.environ['DCA2_PARAMS']).read_bytes()))
    meta.update(dca2_end=os.environ.get('DCA2_END'))
    E4.main(a); s = N4.SPAT.stats
    Path(a.out, f'{a.tag}_n4.json').write_text(json.dumps(dict(n4=N4.A0.n4, gate=N4.gate, q=N4.q, provenance=meta, **s, activation=s['published'] / max(1, s['valid']))))
