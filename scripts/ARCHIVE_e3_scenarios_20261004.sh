#!/usr/bin/env bash
# Archive (not delete) the regenerable CityFlow `scenarios` dirs of FINISHED E3 jobs (04/10/2026 05:5x; disk guard hit 14 GB).
# Each dir -> legacy/scenarios_archive_20261004/<path>.tgz; the original is removed only after the archive lists the same number of files.
cd /Users/phanan/cig-amf-main; A=legacy/scenarios_archive_20261004; mkdir -p "$A"; n=0; bad=0
find research/marl_budget/e3_wave_20261003 -type d -name scenarios | while read -r d; do
  t="$A/$(echo "$d" | tr '/' '_').tgz"; c=$(find "$d" -type f | wc -l | tr -d ' ')
  tar -czf "$t" -C "$(dirname "$d")" scenarios || { echo "TAR FAIL $d"; continue; }
  k=$(tar -tzf "$t" | grep -v '/$' | wc -l | tr -d ' ')
  if [ "$k" = "$c" ] && [ "$c" -gt 0 ]; then rm -r "$d"; echo "archived $d ($c files)"; else echo "MISMATCH $d files $c archive $k (kept)"; fi
done
echo "done $(date)"; df -h /System/Volumes/Data | tail -1
