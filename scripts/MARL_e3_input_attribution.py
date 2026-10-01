#!/usr/bin/env python3
"""D1 (29/09 22:0x, ledger L-121): where does each actor's DECISION draw its sensitivity from?  Offline, no simulator.
Inputs: the 7,776 post-prefix actor inputs of the forced-probe v2 rows (scratch s3 trajectories).  For each actor, the
decision margin = top logit - runner-up logit; attribution = |gradient x input| of the margin, summed per group: own block
(35), agent one-hot (9), message DYNAMIC dims of fresh blocks, of cached (stale) blocks, and the static topology dims.
Reported as shares of the total, and the margin's median.  A descriptive diagnostic (inputs are one actor's trajectory)."""
import glob, json, sys
from pathlib import Path
import numpy as np, torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from models.marl_comm_actor import ActorNet
from models.marl_comm_actor_set import SetActorNet
base = ROOT / 'research/marl_budget/e3_forced_v2_20260929/e3_scratch_seeds34_20260928_actor_s3'
R = []
for d in sorted(x for x in glob.glob(str(base / '*')) if Path(x).is_dir()):
    R += json.loads(Path(d, 'rows.json').read_text())
X = torch.as_tensor(np.array([x for r in R for x in r['x']], np.float32)); L0 = np.array([l for r in R for l in r['logits']]); mask = torch.as_tensor(L0 > -1e8)
D = ROOT / 'research/marl_budget'
actors = {'flat prefix (scratch s3)': D / 'e3_scratch_seeds34_20260928/actor_s3/ckpt_best.pt', 'flat prefix (rs s0)': D / 'e3_scratch_rs_20260928/actor_s0/ckpt_best.pt',
          'flat full s0': D / 'e3_delivery_actors_20260929/full_s0/ckpt_best.pt', 'flat none s0': D / 'e3_delivery_actors_20260929/none_s0/ckpt_best.pt',
          'set prefix s0': D / 'e3_delivery_actors_20260929/set_prefix_s0/ckpt_best.pt', 'set rxq s0': D / 'e3_delivery_actors_20260929/set_rxq_s0/ckpt_best.pt',
          'set full s0': D / 'e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt', 'set none s0': D / 'e3_delivery_actors_20260929/set_none_s0/ckpt_best.pt'}
B0, blk = 44, 29
fresh = X[:, B0::blk][:, :8] > 0.5
for name, p in actors.items():
    ck = torch.load(p, weights_only=False); net = (SetActorNet if ck['config'].get('set_actor') else ActorNet)(X.shape[1], ck['config']['hidden'])
    net.load_state_dict(ck['actor']); net.eval()
    x = X.clone().requires_grad_(True); lg = net(x, mask); top2 = lg.topk(2, -1).values; margin = top2[:, 0] - top2[:, 1]
    margin.sum().backward(); A = (x.grad * x).abs().detach().numpy()
    own = A[:, :35].sum(1); oh = A[:, 35:44].sum(1)
    dyn = np.stack([A[:, B0 + k * blk: B0 + k * blk + 21].sum(1) for k in range(8)], 1); st = np.stack([A[:, B0 + k * blk + 21: B0 + (k + 1) * blk].sum(1) for k in range(8)], 1)
    fr = fresh.numpy(); tot = own + oh + dyn.sum(1) + st.sum(1)
    sh = lambda v: float(np.mean(v / tot))
    print(f'{name:26s} own {sh(own):.2f} | onehot {sh(oh):.2f} | msg fresh {sh((dyn * fr).sum(1)):.2f} | msg stale {sh((dyn * ~fr).sum(1)):.2f} | static {sh(st.sum(1)):.2f} | median margin {np.median(margin.detach().numpy()):.2f}')
