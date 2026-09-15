from pathlib import Path
import os,subprocess,sys,time
base=Path(__file__).resolve().parent
root=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
env=dict(os.environ,LEAN_PATH=':'.join([str(base),str(root)]+[str(p) for p in (root/'.lake/packages').glob('*/.lake/build/lib/lean')]))
for name in sys.argv[1:]:
 p=base/name
 t=time.time()
 result=subprocess.run(['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','--incr-header-save='+str(p.with_suffix('.header')), *(['--incr-load='+str(p.with_suffix('.header'))] if p.with_suffix('.header').exists() else []), '-o',str(p.with_suffix('.olean')),str(p)],env=env,capture_output=True,text=True)
 log=result.stdout+result.stderr
 p.with_suffix('.log').write_text(log)
 print(name,'exit',result.returncode,'seconds',round(time.time()-t,2),flush=True)
 print(log,flush=True)
 if result.returncode:sys.exit(result.returncode)
