from layers import *
import numpy as np
for m in [5,7,9,11,13]:
    w,n=family(m);D=m+4
    print('m',m)
    for k in range(1,m):
        vals=[layer(w,n,k,e)*m*D for e in np.arange(0,1.01,0.05)]
        # find zero point
        print('  k',k,' '.join('%.2f'%v for v in vals))
