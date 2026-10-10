# rand3 network build record (W8-4, PROTOCOL_CITY_WAVE8_20261005), 05/10 16:06
1. netgenerate --rand --rand.iterations 45 --rand.bidi-probability 1 --rand.min-distance 140 --rand.max-distance 320 --rand.min-angle 60 --rand.neighbor-dist5 0 --rand.neighbor-dist6 0 --seed 7 --default.lanenumber 1 --default.speed 13.89 --tls.guess true --tls.guess.threshold 0 --tls.default-type static --tls.layout opposites --tls.green.time 42 --tls.yellow.time 3 --no-turnarounds true  (SUMO 1.27.1)
2. 21 signals; the one with != 2 greens unset: netconvert -s r0.net.xml --tls.unset 1 -o rand3.net.xml
3. Result: 20 signals, all programs (42, 3, 42, 3); 104 edges; mean edge 231 m. sha256 5ac951714a2083bb
