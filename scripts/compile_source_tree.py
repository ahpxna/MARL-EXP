"""Compile every Python source file in the source tree without executing labs."""
from __future__ import annotations
import argparse,json,py_compile,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
EXCLUDED={'__pycache__','.pytest_cache','.mypy_cache','.ruff_cache','research','compile_logs','outputs','results','wandb','__MACOSX','.git','.venv','.lake'}
# Archive/OS debris that is not scientific source.  AppleDouble sidecars ('._x.py')
# are byte-for-byte not Python and make a raw `pytest -q` on an unpacked ZIP fail
# at COLLECTION, which reads like a source failure and is not one.  '*.rej' files
# are leftovers from a failed patch apply and must never be compiled or shipped.
EXCLUDED_NAME_PREFIXES=('._',)
EXCLUDED_NAMES={'.DS_Store'}
EXCLUDED_SUFFIXES=('.rej','.orig')


def is_archive_debris(rel) -> bool:
    for part in rel.parts:
        if part in EXCLUDED_NAMES or part.startswith(EXCLUDED_NAME_PREFIXES):
            return True
        if part.endswith(EXCLUDED_SUFFIXES):
            return True
    return False

def run(root: Path=ROOT):
    files=[]; errors=[]
    for p in sorted(root.rglob('*.py')):
        rel=p.relative_to(root)
        if any(part in EXCLUDED for part in rel.parts): continue
        if is_archive_debris(rel): continue
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
