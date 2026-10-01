from ilp import *
from fractions import Fraction as Fr
cases=[
 ("V0 lo", [(1,1),(2,1)], [0, Fr(3,4)], 'lo', 0.0),
 ("V0 mid1", [(2,1),(Fr(7,3),1)], [Fr(3,4), Fr(5-Fr(7,3),4)], 'mid', 0.0),
 ("V0 mid2", [(Fr(7,3),1),(3,1)], [Fr(2,3), 1], 'mid', 0.0),
 ("V0 hi", [(3,1),(1,0)], [1, Fr(1,2)], 'hi', 0.0),
 ("Vf lo", [(1,1),(2,1)], [0, Fr(2,3)], 'lo', None),
 ("Vf 4/7", [(Fr(17,7),1),(3,1)], [Fr(4,7), Fr(4,7)], 'mid', None),
 ("Vf hi", [(3,1),(1,0)], [Fr(4,7), Fr(2,7)], 'hi', None),
]
for name,ends,W,reg,eta in cases:
    ends=[(float(a),float(b)) for a,b in ends]
    res=ilp(ends,W,reg,eta)
    print(name)
    show(res,ends,reg)
