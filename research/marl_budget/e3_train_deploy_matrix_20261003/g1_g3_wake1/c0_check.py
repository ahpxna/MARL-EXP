import sys, time, numpy as np
sys.path.insert(0, '/private/tmp/claude-502/-Users-phanan-cig-amf-main/976002e4-6f9b-4c75-8890-ea54dcea033f/scratchpad/agentB')
from c0_exact import *
t0 = time.time(); torch.set_num_threads(1)
L = 'ACT'; V, Q, h = tables(L); TM = V.shape[3]
pi_star = Q.argmin(-1); r = evaluate(pi_star, L, V, Q, h)
P = np.load(O / 'panels' / f'{L}_eval.npz'); R0 = dict(np.load(O / 'seed_0' / 'regrets.npz'))
print(L, 'Z* exact E[cost] %.3f timeout %.4f | panel mean cost %.3f (topt %.3f + regret %.3f), se %.3f | PDL %.4f  [%.0fs]' % (
    r['cost'], r['alive'], P['topt'].mean() + R0['Z*_ACT|ACT|plain'].mean(), P['topt'].mean(), R0['Z*_ACT|ACT|plain'].mean(),
    (P['topt'] + R0['Z*_ACT|ACT|plain']).std() / np.sqrt(3000), r['pdl'], time.time() - t0))
net = load_net(0); pi = net_actions(net, TM); r2 = evaluate(pi, L, V, Q, h)
print('Z_ACT s0 on ACT exact E[cost] %.3f timeout %.4f | panel %.3f | exact excess %.3f vs panel excess %.3f | PDL %.3f  [%.0fs]' % (
    r2['cost'], r2['alive'], P['topt'].mean() + R0['Z_ACT|ACT|plain'].mean(), r2['cost'] - r['cost'], (R0['Z_ACT|ACT|plain'] - R0['Z*_ACT|ACT|plain']).mean(), r2['pdl'], time.time() - t0))
