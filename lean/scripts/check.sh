#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
export LEAN_NUM_THREADS=1
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]]; then
    lake exe cache get
fi
python3 scripts/build.py
python3 scripts/audit.py
