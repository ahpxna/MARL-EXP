#!/usr/bin/env python3
"""Run one command with a STALL watchdog, retrying on hang (CityFlow barrier deadlock, 28/09/2026).

Observed: CityFlow's engine can block forever in its thread barrier (pthread_cond_wait) while holding
the GIL, under heavy CPU oversubscription and after a system sleep, so an in-process timeout cannot
fire.  This wrapper runs the command with stdout/stderr to --log, and if the log's size and mtime do
not change for --stall seconds it kills THAT child (SIGTERM, then SIGKILL), moves the command's
--out directory (if any) to legacy/<name>_stalled_<k>_<timestamp> (never deleted), and retries up to
--retries times.  Exit code: the command's own, or 124 after the last stalled attempt.
Usage: run_with_watchdog.py --log L [--out DIR] [--stall S] [--retries N] -- cmd args...
"""
from __future__ import annotations
import argparse, os, shutil, signal, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(); p.add_argument('--log', required=True); p.add_argument('--out')
    p.add_argument('--stall', type=float, default=1800); p.add_argument('--retries', type=int, default=3)
    p.add_argument('cmd', nargs=argparse.REMAINDER); a = p.parse_args()
    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == '--' else a.cmd
    log = Path(a.log)
    for attempt in range(a.retries + 1):
        with open(log, 'ab') as fh:
            fh.write(f'\n[watchdog] attempt {attempt} {time.ctime()}: {" ".join(cmd)}\n'.encode()); fh.flush()
            proc = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT)
            last = (log.stat().st_size, log.stat().st_mtime); t_last = time.time()
            while proc.poll() is None:
                time.sleep(10)
                cur = (log.stat().st_size, log.stat().st_mtime)
                if cur != last:
                    last, t_last = cur, time.time()
                elif time.time() - t_last > a.stall:
                    proc.send_signal(signal.SIGTERM)
                    try:
                        proc.wait(30)
                    except subprocess.TimeoutExpired:
                        proc.kill(); proc.wait()
                    break
        if proc.returncode is not None and proc.returncode >= 0 and time.time() - t_last <= a.stall:
            return proc.returncode
        with open(log, 'ab') as fh:
            fh.write(f'[watchdog] STALL after {a.stall:.0f}s without log output; child killed {time.ctime()}\n'.encode())
        if a.out and Path(a.out).exists():
            dst = ROOT / 'legacy' / f'{Path(a.out).name}_stalled_{attempt}_{time.strftime("%Y%m%d_%H%M%S")}'
            shutil.move(a.out, dst)
            with open(log, 'ab') as fh:
                fh.write(f'[watchdog] partial output moved to {dst}\n'.encode())
    return 124


if __name__ == '__main__':
    sys.exit(main())
