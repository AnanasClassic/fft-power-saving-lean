#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_inventory.py
python3 scripts/verify_core.py
python3 scripts/verify_array.py
python3 scripts/moment_certificate.py
printf 'PASS_PYTHON_PREFLIGHT_ONLY (not Lean verification)\n'
