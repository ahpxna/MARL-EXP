"""Compile every Python source file in the source tree without executing labs."""
from __future__ import annotations
import argparse,json,py_compile,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
EXCLUDED={'__pycache__','.pytest_cache','.mypy_cache','.ruff_cache','research','compile_logs','outputs','results','wandb','__MACOSX'}

def run(root: Path=ROOT):
    files=[]; errors=[]
    for p in sorted(root.rglob('*.py')):
        rel=p.relative_to(root)
        if any(part in EXCLUDED for part in rel.parts): continue
        files.append(p)
        try: py_compile.compile(str(p),doraise=True)
        except Exception as exc: errors.append({'path':str(rel),'error':f'{type(exc).__name__}: {exc}'})
    return {'root':str(root),'python_files':len(files),'error_count':len(errors),'errors':errors,'pass':not errors}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--root',default=str(ROOT)); p.add_argument('--out',default=None); a=p.parse_args(argv)
    payload=run(Path(a.root).resolve())
    if a.out:
        Path(a.out).parent.mkdir(parents=True,exist_ok=True); Path(a.out).write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(payload,indent=2)); return 0 if payload['pass'] else 2
if __name__=='__main__': raise SystemExit(main())
