#!/usr/bin/env bash
# Final Midtown report over every arm present (MT-A3/A4/A5); runs even if an earlier job failed.
set -u; cd /Users/phanan/cig-amf-main; external_envs/city_runtime/bin/python scripts/MT_report.py; date
