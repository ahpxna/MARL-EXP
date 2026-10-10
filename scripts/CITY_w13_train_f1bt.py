#!/usr/bin/env python3
"""W13-5 F1B-T trainer (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): CITY_fleet_train_f1b.py (unchanged, imported) with TSI in force during
training, installed by monkey-patching (no existing file is edited):
  * provider: C2.make_spat_c2 is replaced by the TSI fleet side, the N4 hybrid provider CITY_spat_forecast_n4 (gate hyb:<table>) on the
    light's state model at quantile Q4 (W13_N4="<q>:<table>:<model>"); its N2 Tracker is reset per episode and stepped every second after
    the cars (CarPPOL.step), the order of CITY_eval_n4 (light, cars, logger + tracker);
  * light: CE.LightRL(info, policy) is replaced by CITY_eval4.LightRLX(info, policy, adapter='q:A:B') (W13_AB="A:B"), the TSI light side.
Everything else (PPO recipe, 200 episodes, TRAIN seeds, scratch init, logging, save format) is the F1-B trainer's.  The saved file records
the TSI provider and adapter.  Usage: W13_N4=... W13_AB=... CITY_w13_train_f1bt.py <CITY_fleet_train_f1b.py args>"""
import hashlib, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w8_run  # noqa: E402,F401  (light_spec patch RL-H 4..18)
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
import scripts.CITY_spat_forecast_n2 as N2  # noqa: E402
import scripts.CITY_spat_forecast_n4 as N4  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import torch  # noqa: E402
import scripts.CITY_fleet_train_f1b as T  # noqa: E402

q, table, model = os.environ['W13_N4'].split(':', 2); q = float(q); A, B = os.environ['W13_AB'].split(':')
INFO = E4.NetInfo(E4.Q7.NET_S); TR = N2.Tracker(); IDS = sorted(INFO.tls)
SPAT = N4.make_spat_n4(model, q, INFO, TR, f'hyb:{table}')
C2.make_spat_c2 = lambda tab, qq: (SPAT, None)  # noqa: E731
_Car = V11.CarPPOL


class CarT(_Car):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); TR.__init__()

    def step(self, t):
        super().step(t); TR.step(IDS)


V11.CarPPOL = CarT
CE.LightRL = lambda info, pol: E4.LightRLX(info, pol, adapter=f'q:{A}:{B}')  # noqa: E731
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()  # noqa: E731
_save = torch.save


def save(obj, f, *a, **k):
    if isinstance(obj, dict) and obj.get('kind') == 'ppo_residual_glosaL':
        obj.update(w13_tsi=dict(n4=os.environ['W13_N4'], ab=os.environ['W13_AB'], model_sha256=sha(model), table_sha256=sha(table),
                                runner_sha256=sha(__file__), provider_stats=dict(getattr(SPAT, 'stats', {})),
                                light_class=CE.LightRL(INFO, lambda O: 0).__class__.__name__))
    return _save(obj, f, *a, **k)


T.torch.save = save
if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--seed', type=int, required=True); p.add_argument('--light-k', type=int, required=True); p.add_argument('--init', required=True)
    p.add_argument('--table', required=True); p.add_argument('--q', type=float, required=True); p.add_argument('--episodes', type=int, required=True)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    T.main(p.parse_args())
