"""Regression checks for nuisance-domain semantics, independent of optimizers."""
from fractions import Fraction as F
from pathlib import Path
import json
from approximate_game import solve
checks=0
for d in range(6):
    for eps in map(F,['0','1/2','3/4','1','3/2','2','5']):
        for nu in map(F,['0','1/4','1/2','3/4','1']):
            bad=eps<(2-nu)*d/2
            interval=d>0 and 0<=nu<=1 and nu<2-2*eps/d
            assert bad==interval
            checks+=1
        assert (eps<d)==(eps<(2-F(0))*d/2)
# True-mu substitution loses a genuinely bad alternative.
assert (2-F('1/2'))/2<=F('4/5') and F('4/5')<(2-F(0))/2
# An excluded upper endpoint may achieve the closure infimum, but is not bad.
eps=F('3/4');upper=2-2*eps
assert upper==F('1/2') and not eps<(2-upper)/2
for n in [2,10,100,1000]:
    nu=upper-upper/n
    assert eps<(2-nu)/2 and (nu-upper)**2>0
# Positive-cost game domain and answer validity are enforced before construction.
rejected=0
for args in [(3,0,.5,3),(3,1,.5,0),(3,0,1.1,0),(1,0,.5,0),(3,0,.5,-.1)]:
    try:solve(*args)
    except ValueError:rejected+=1
assert rejected==5
Path(__file__).with_suffix('.json').write_text(json.dumps({'passed':True,'rational_interval_checks':checks,
 'true_mu_substitution_negative_control':True,'excluded_endpoint_negative_control':True,
 'invalid_solver_inputs_rejected':rejected},indent=2)+'\n')
print(checks,'rational cases; five invalid solver inputs rejected')
