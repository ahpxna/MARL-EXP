from pathlib import Path
import json,subprocess,sys
r=Path(__file__).resolve().parent
raise SystemExit(subprocess.run([sys.executable,str(r/'compile.py')]+json.loads((r/'dependency_order.json').read_text())).returncode)
