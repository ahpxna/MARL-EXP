#!/usr/bin/env bash
# Sequential job spool, night 04→05/10 (user 23:0x: "máy đang nặng r, đừng chạy thêm nữa, nếu có thì bỏ vào queue đi, r chờ"); copy of RUN_spool_20261004.sh with its own queue.
# Waits for the PIDs in WAIT_PIDS, then runs research/queue_spool_20261004/pending/*.sh ONE AT A TIME in name order (each job uses at
# most its own LANES, OMP_NUM_THREADS=1).  Jobs added later are picked up; the runner exits after IDLE_MAX seconds with nothing pending
# (bounded).  A job file is moved pending -> running -> done | failed; its output goes to logs/<job>.log.  Disk guard 15 GB.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; Q=research/queue_night_20261005; IDLE_MAX=${IDLE_MAX:-10800}
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONHASHSEED=0
echo "spool start $(date); waiting for: ${WAIT_PIDS:-none}"
for p in ${WAIT_PIDS:-}; do caffeinate -w "$p" 2>/dev/null; done
echo "spool active $(date)"; idle=0
while [ "$idle" -lt "$IDLE_MAX" ]; do
  j=$(ls "$Q/pending/" 2>/dev/null | grep '\.sh$' | sort | head -1)
  if [ -z "$j" ]; then sleep 60; idle=$((idle + 60)); continue; fi
  idle=0; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
  if [ "${f:-0}" -lt 15 ]; then echo "REFUSED $j: $f GB free $(date)"; sleep 600; continue; fi
  mv "$Q/pending/$j" "$Q/running/$j"; echo "job $j start $(date)"
  if bash "$Q/running/$j" > "$Q/logs/${j%.sh}.log" 2>&1; then mv "$Q/running/$j" "$Q/done/$j"; echo "job $j done $(date)"
  else mv "$Q/running/$j" "$Q/failed/$j"; echo "job $j FAILED $(date)"; fi
done
echo "spool idle for ${IDLE_MAX}s, exit $(date)"
