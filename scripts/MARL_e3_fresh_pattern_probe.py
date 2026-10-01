"""Offline check (no simulator): how much does the scratch-s3 actor's action depend on the delivery PATTERN
(fresh flag / age of each sender slot) rather than the message CONTENT?  Inputs: the post-prefix actor inputs x
stored by MARL_e3_forced_action_probe_v2 (train/select/dev rows).  Block layout from models/marl_comm_actor.py:
own 35 | agent onehot 9 | 8 x [fresh, heard, age/100, phase onehot 9, elapsed/100, veh/30 x4, wait/30 x4, static 8]."""
import glob, json, sys
from pathlib import Path
import numpy as np, torch
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
from models.marl_comm_actor import ActorNet

base = ROOT / 'research/marl_budget/e3_forced_v2_20260929/e3_scratch_seeds34_20260928_actor_s3'
R = []
for d in sorted(x for x in glob.glob(str(base / '*')) if Path(x).is_dir()):
    R += json.loads(Path(d, 'rows.json').read_text())
man = json.loads((ROOT / json.loads(Path(base, 'dev_0', 'manifest.json').read_text())['args']['actor_dir'] / 'labels_dev' / 'manifest.json').read_text())
ck = torch.load(ROOT / man['args']['ckpt'] if not Path(man['args']['ckpt']).is_absolute() else man['args']['ckpt'], weights_only=False)
X = np.array([r['x'] for r in R], np.float32)            # (states, 9, 276)
L0 = np.array([r['logits'] for r in R], np.float32)
S, M, D = X.shape; mask = torch.as_tensor(L0 > -1e8)
net = ActorNet(D, ck['config']['hidden']); net.load_state_dict(ck['actor']); net.eval()
def act(x):
    with torch.no_grad():
        return net(torch.as_tensor(x.reshape(S * M, D)), mask.reshape(S * M, -1)).numpy().reshape(S, M, -1).argmax(-1)
a0 = act(X); print(f'states {S}, receivers {S*M}; reproduces stored argmax: {(a0 == L0.argmax(-1)).mean():.4f}')
B0 = 44; blk = 29
F = X[:, :, B0::blk][:, :, :8]; H = X[:, :, B0 + 1::blk][:, :, :8]
W = np.stack([X[:, :, B0 + 17 + k::blk][:, :, :8] for k in range(4)], -1).sum(-1) * 30
print(f'fresh slots per receiver {F.sum(-1).mean():.2f} of 8; heard {H.sum(-1).mean():.2f}')
print(f'content waiting (sum over approaches) of FRESH senders {W[F > 0.5].mean():.2f} vs CACHED heard senders {W[(F < 0.5) & (H > 0.5)].mean():.2f}')

def perturb(fn):
    x = X.copy(); fn(x); a = act(x); return float((a != a0).mean())
def slots(x):
    for k in range(8):
        yield x[:, :, B0 + k * blk: B0 + (k + 1) * blk]
def fresh_zero(x):
    for b in slots(x): b[..., 0] = 0.0
def fresh_all(x):                          # pattern of "everyone delivered now", content unchanged
    for b in slots(x): b[..., 0] = b[..., 1]; b[..., 2] = 0.0
def age_zero(x):
    for b in slots(x): b[..., 2] = 0.0
rng = np.random.default_rng(0)
def fresh_perm(x):                         # same number of fresh slots, randomly re-assigned among heard senders
    for s in range(S):
        for i in range(M):
            blocks = [x[s, i, B0 + k * blk: B0 + (k + 1) * blk] for k in range(8)]
            heard = [k for k in range(8) if blocks[k][1] > 0.5]; fr = [blocks[k][0] for k in heard]; ag = [blocks[k][2] for k in heard]
            p = rng.permutation(len(heard))
            for n, k in enumerate(heard):
                blocks[k][0] = fr[p[n]]; blocks[k][2] = ag[p[n]]
def content_perm(x):                       # payload content permuted among heard senders, pattern kept (msguse 'shuffle')
    for s in range(S):
        for i in range(M):
            blocks = [x[s, i, B0 + k * blk: B0 + (k + 1) * blk] for k in range(8)]
            heard = [k for k in range(8) if blocks[k][1] > 0.5]; c = [blocks[k][3:21].copy() for k in heard]
            p = rng.permutation(len(heard))
            for n, k in enumerate(heard):
                blocks[k][3:21] = c[p[n]]
for name, fn in (('fresh flags all 0 (content, age kept)', fresh_zero), ('age all 0 (fresh, content kept)', age_zero),
                 ('fresh=1, age=0 for every heard sender (content kept)', fresh_all),
                 ('fresh/age pattern permuted among heard senders (content kept)', fresh_perm),
                 ('content permuted among heard senders (pattern kept)', content_perm)):
    print(f'action change rate | {name:62s} {perturb(fn):.3f}')
