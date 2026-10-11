#!/usr/bin/env python3
"""Writes the job that follows 039 (PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004.md §After 039, registered 05:56): B6-2 for a passing v4
class, otherwise the B6-R recipe screen.  Prepared 04/10/2026 05:5x (wake 4)."""
import json, sys
from pathlib import Path
W = Path('research/city_sim/wave2_20261004'); P = Path('research/queue_spool_20261004/pending'); O = 'research/city_sim/fleet_upgrade_20261004'
HDR = 'cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python\n'
f = W / '039' / 'b6_verdicts.json'
v = json.loads(f.read_text()) if f.exists() else {}
passing = sorted({k.rsplit('_t', 1)[0] for k, ok in v.items() if ok})
if passing:
    rec = passing[0]; act = 'release' if 'v4rel' in rec else 'residual'; base = rec[2:] if rec.startswith('U-') else rec
    train = '\n'.join(f'echo "{act} {13 + 100 * t} {base}_t{t}"' for t in (2, 3))
    evals = '\n'.join(f'echo "--light ACT --fleet U:{base}_t{t} --seeds 400 401 402 403 404 405 406 407 408 409 --tag U-{base}_t{t}_ACT"' for t in (2, 3))
    job = P / '040_B6_2_v4.sh'
    job.write_text(f"# 040 B6-2 for the v4 class {base} (written by CITY_make_b6_next.py)\n{HDR}"
                   f"{{ {train}; }} | xargs -P 2 -L 1 sh -c 'nice -n 5 '\"$PY\"' -u scripts/CITY_fleet_train_v4.py --actions $0 --fleet-seed $1 --name $2 --out {O} > {O}/$2.out 2>&1 || echo \"FAIL $2\"'\n"
                   f"mkdir -p {W}/040/tmp; export XPLAY_TMP=$PWD/{W}/040/tmp\n"
                   f"{{ {evals}; echo \"--light ACT --fleet L-ACT:0 --guard always --seeds 400 401 402 403 404 405 406 407 408 409 --tag OFF_ACT\"; }} | "
                   f"xargs -P 4 -L 1 sh -c 'nice -n 5 '\"$PY\"' -u scripts/CITY_eval4.py \"$@\" --out {W}/040 >> {W}/040/run.log 2>&1 || echo \"FAIL $*\"' sh\n"
                   f"$PY -c \"import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R; out = []; R.rb6(out, R.W / '040', list(range(400, 410)), '-2 v4 confirmation'); print(chr(10).join(out))\"\n")
else:
    arms = [('v3', 'acc', 'R1'), ('cotv', 'acc', 'R2'), ('cotv', 'release', 'R3'), ('v3', 'fine', 'R4')]
    train = '\n'.join(f'echo "{r} {a} {13 + 100 * t} L-ACT-{n}_t{t}"' for r, a, n in arms for t in (0, 1))
    evals = '\n'.join(f'echo "--light ACT --fleet U:L-ACT-{n}_t{t} --seeds 100 101 102 103 104 --tag U-L-ACT-{n}_t{t}_ACT"' for _, _, n in arms for t in (0, 1))
    job = P / '040_B6R_recipes.sh'
    job.write_text(f"# 040 B6-R recipe screen (written by CITY_make_b6_next.py): R1 v3/acc, R2 cotv/acc, R3 cotv/release, R4 v3/fine, 480 episodes, seeds 13/113\n{HDR}"
                   f"{{ {train}; }} | xargs -P 8 -L 1 sh -c 'nice -n 5 '\"$PY\"' -u scripts/CITY_fleet_train_v5.py --reward $0 --actions $1 --fleet-seed $2 --name $3 --episodes 480 --out {O} > {O}/$3.out 2>&1 || echo \"FAIL $3\"'\n"
                   f"mkdir -p {W}/040/tmp; export XPLAY_TMP=$PWD/{W}/040/tmp\n"
                   f"{{ {evals}; echo \"--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT\"; }} | "
                   f"xargs -P 4 -L 1 sh -c 'nice -n 5 '\"$PY\"' -u scripts/CITY_eval4.py \"$@\" --out {W}/040 >> {W}/040/run.log 2>&1 || echo \"FAIL $*\"' sh\n"
                   f"$PY -c \"import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R; out = []; R.rb6(out, R.W / '040', R.SEL, '-R recipe screen'); t = chr(10).join(out); open(str(R.W / 'report_v2_b6R.txt'), 'w').write(t); print(t)\"\n")
print('wrote', job)
