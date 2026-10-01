#!/usr/bin/env bash
# Pre-launch guard (28/09 double-writer incident, ledger L-53): list every live process whose command line mentions
# any of the given directories, and exit 3 if there is one.  Run it immediately before launching a runner on a dir.
# Usage: bash scripts/e3_writers_check.sh <dir> [<dir> ...]
rc=0
for d in "$@"; do
  hits=$(ps -eo pid,etime,command | grep -F -- "$d" | grep -v -e "e3_writers_check" -e "grep -F" | grep -v "^ *$$ ")
  if [ -n "$hits" ]; then echo "BUSY $d:"; echo "$hits" | cut -c1-160; rc=3; else echo "free $d"; fi
done
exit $rc
