#!/bin/bash
set -euo pipefail
cd '/Users/phanan/cig-amf-main'
# Downloads/rebuilds deleted dependencies; does not rerun experiments.
python3.14 -m venv '.venv'
'.venv'/bin/python -m pip install -r '/Users/phanan/cig-amf-main/maintenance/disk-cleanup-20261115T023655Z/.venv-requirements.txt'
python3.12 -m venv 'external_envs/runtime'
'external_envs/runtime'/bin/python -m pip install -r '/Users/phanan/cig-amf-main/maintenance/disk-cleanup-20261115T023655Z/external_envs__runtime-requirements.txt'
bash scripts/setup_external_envs.sh --install
python3.12 -m venv 'external_envs/city_runtime'
'external_envs/city_runtime'/bin/python -m pip install -r '/Users/phanan/cig-amf-main/maintenance/disk-cleanup-20261115T023655Z/external_envs__city_runtime-requirements.txt'
python3.14 -m venv 'external_envs/data_runtime'
'external_envs/data_runtime'/bin/python -m pip install -r '/Users/phanan/cig-amf-main/maintenance/disk-cleanup-20261115T023655Z/external_envs__data_runtime-requirements.txt'
cd work/p13_conjectures
lake exe cache get
# Local Lean source, dependency checkouts, manifests and proof receipts were retained.
