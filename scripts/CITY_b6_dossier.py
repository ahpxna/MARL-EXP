#!/usr/bin/env python3
"""B6 dossier (04/10/2026 wake 4): one table over every beneficial-fleet attempt, each with its validity label, using the SAME B6-1 report
function (CITY_wave2_report_v2.rb6) on every evaluation directory.  Labels:
  valid        trainer free of the C-22 contamination (v3 / v4-release by the reward signature; v1 / v2 measured; v6 sanitized; BC)
  VOID         contaminated (job 039 residual arm; job 040 R4); shown for completeness, never used for a decision
  unsanitized  v5 arms without the teleport guard and without a reward signature (job 040 R1-R3); decisions use their v6 reruns (040c)"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

DIRS = [('036', 'B6-1 screen: v2 / v3 (ACC)', {}), ('039', 'B6-N policy class (v4)', {'v4res': 'VOID (C-22)'}),
        ('040', 'B6-R recipes, v5', {'R4': 'VOID (C-22)', 'R1': 'unsanitized', 'R2': 'unsanitized', 'R3': 'unsanitized'}),
        ('040b', 'B6-N residual rerun, v6', {}), ('040c', 'B6-R recipes rerun, v6', {}), ('040d', 'B6-I behaviour cloning', {})]


def main():
    out = ['== B6 dossier: every fleet vs always-SUMO (SUMO default driver model) on the same vehicles, ACT, SELECT 100-104']
    for d, title, labels in DIRS:
        sub = []
        R.rb6(sub, R.W / d, R.SEL, f' [{title}]')
        for line in sub:
            lab = next((v for k, v in labels.items() if k in line), 'valid' if line.strip().startswith('U-') else '')
            out.append(line + (f'   <{lab}>' if lab and line.strip().startswith('U-') else ''))
    txt = '\n'.join(out) + '\n'; (R.W / 'B6_DOSSIER.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main()
