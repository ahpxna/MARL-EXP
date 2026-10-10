#!/usr/bin/env python3
"""W15-2b (PROTOCOL_CITY_WAVE15_20261007): state-dependent published quantile.  Wraps CITY_n2_fit.QNet (the N2 / N4 forecaster network;
no file is edited): the q0.1 output column is replaced by the interpolated quantile
    tau = 0.1 + 0.4 * sigmoid(a - b * w / 10 - c * h / 30),   w = max(0, p0.5 - p0.1),  h = max(0, p0.5)   (seconds)
    p(tau) = p0.1 + (tau - 0.1) / 0.4 * (p0.5 - p0.1)
so a provider run at q = 0.1 (CITY_eval_n4 --n4 0.1:hyb:...) publishes p(tau); the q0.5 column is unchanged; the yellow (c2 table) branch
stays at q 0.1.  Confident answers (small w, short h) move towards the median, uncertain ones stay at q 0.1.  Env W15_QS="a:b:c".
Rows get w15_qs.  Usage: W15_QS=a:b:c CITY_w15_qstate.py <target script> <its args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import torch  # noqa: E402
import scripts.CITY_n2_fit as NF  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
A, B, C = (float(x) for x in os.environ['W15_QS'].split(':')); I1, I5 = list(NF.QS).index(0.1), list(NF.QS).index(0.5)
_Q = NF.QNet


class QNetS(_Q):
    def forward(self, x):
        y = super().forward(x); p1, p5 = y[..., I1], y[..., I5]
        w = (p5 - p1).clamp(min=0.0); h = p5.clamp(min=0.0)
        tau = 0.1 + 0.4 * torch.sigmoid(A - B * w / 10.0 - C * h / 30.0)
        y = y.clone(); y[..., I1] = p1 + (tau - 0.1) / 0.4 * (p5 - p1); return y


NF.QNet = QNetS
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); out['w15_qs'] = os.environ['W15_QS']; return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w15qs:{os.environ['W15_QS']}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
