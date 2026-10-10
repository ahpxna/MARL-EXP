#!/usr/bin/env python3
"""B6-SL-V (PROTOCOL_CITY_B6 §B6-SL-V): CITY_b6sl_report.main on VALIDATION 200-209, directory wave2_20261004/049v; writes report_b6sl_val.txt."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_b6sl_report as M  # noqa: E402
M.D = M.R.W / '049v'; M.SEL = list(range(200, 210))
_orig_write = Path.write_text
Path.write_text = lambda self, txt, *a, **k: _orig_write(self.with_name('report_b6sl_val.txt') if self.name == 'report_b6sl.txt' else self, txt, *a, **k)
M.main()
