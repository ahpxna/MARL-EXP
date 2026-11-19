#!/usr/bin/env bash
# Linux + NVIDIA (RTX 4090) setup of the two runtimes the run scripts call (user 18/11/2026).
#   external_envs/city_runtime : SUMO 1.27.1 (libsumo, traci) + CUDA torch      -> CITY_* scripts
#   external_envs/runtime      : MARL benchmarks (scripts/setup_external_envs.sh) + CUDA torch -> MARL_* scripts
# Usage, from a fresh clone:
#   git clone https://github.com/ahpxna/MARL-EXP.git cig-amf-main && cd cig-amf-main && bash scripts/setup_linux_gpu.sh
# Options: --city-only (skip the MARL runtime), TORCH_VERSION=2.10.0 (default), TORCH_INDEX=https://download.pytorch.org/whl/cu128
set -euo pipefail
cd "$(dirname "$0")/.."
TORCH_VERSION="${TORCH_VERSION:-2.10.0}"; TORCH_INDEX="${TORCH_INDEX:-}"
CITY_ONLY=0; [ "${1:-}" = "--city-only" ] && CITY_ONLY=1

command -v nvidia-smi >/dev/null && nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv || echo "WARNING: nvidia-smi not found"
echo "CPU cores: $(nproc)  RAM: $(free -g | awk '/Mem:/{print $2}') GB  disk free: $(df -h . | awk 'NR==2{print $4}')"

mkvenv() {   # python 3.12 venv; uv fetches 3.12 when the system has none
  if command -v python3.12 >/dev/null; then python3.12 -m venv "$1"
  elif command -v uv >/dev/null; then uv venv --python 3.12 --seed "$1"
  else echo "need python3.12 or uv (curl -LsSf https://astral.sh/uv/install.sh | sh)"; exit 1; fi
  "$1/bin/python" -m pip install --upgrade pip 'setuptools<81' wheel -q
}
torch_install() {   # PyPI Linux x86_64 torch wheels are CUDA builds; TORCH_INDEX picks a specific CUDA wheel set
  if [ -n "$TORCH_INDEX" ]; then "$1/bin/python" -m pip install "torch==$TORCH_VERSION" --index-url "$TORCH_INDEX"
  else "$1/bin/python" -m pip install "torch==$TORCH_VERSION"; fi
}

[ -x external_envs/city_runtime/bin/python ] || mkvenv external_envs/city_runtime
external_envs/city_runtime/bin/python -m pip install -r requirements-linux-city.txt
torch_install external_envs/city_runtime

if [ "$CITY_ONLY" = 0 ]; then
  [ -x external_envs/runtime/bin/python ] || mkvenv external_envs/runtime
  external_envs/runtime/bin/python -m pip install -r requirements-linux-marl.txt || echo "WARNING: some pinned MARL packages failed; see above"
  torch_install external_envs/runtime
  CIG_EXTERNAL_PYTHON="$(pwd)/external_envs/runtime/bin/python" bash scripts/setup_external_envs.sh --install || echo "WARNING: external benchmark install failed; see above"
fi

for py in external_envs/city_runtime/bin/python external_envs/runtime/bin/python; do
  [ -x "$py" ] && "$py" -c "import torch; print('$py', torch.__version__, 'cuda', torch.cuda.is_available(), torch.cuda.get_device_name(0) if torch.cuda.is_available() else '')"
done
external_envs/city_runtime/bin/python -c "import libsumo, sumolib; print('SUMO OK', libsumo.__file__)"
echo "Next: PYTHONHASHSEED=0 OMP_NUM_THREADS=1 external_envs/city_runtime/bin/python -u scripts/GPU_check.py"
