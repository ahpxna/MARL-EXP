"""Run the repository test suite without ambient third-party pytest plugins.

Some managed runtimes auto-load unrelated pytest plugins that can hang during
interpreter shutdown after all CIG-AMF tests have passed.  Release validation
must be a property of this repository, not of whatever plugins happen to be
installed globally, so this wrapper disables plugin autoload in a clean child
process and forwards any extra pytest arguments.
"""
from __future__ import annotations
import os, subprocess, sys


def main(argv=None):
    args=list(sys.argv[1:] if argv is None else argv)
    env=os.environ.copy(); env['PYTEST_DISABLE_PLUGIN_AUTOLOAD']='1'
    cmd=[sys.executable,'-m','pytest'] + (args if args else ['-q'])
    return int(subprocess.run(cmd,env=env,check=False).returncode)

if __name__=='__main__': raise SystemExit(main())
