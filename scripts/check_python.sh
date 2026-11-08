#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_inventory.py
python3 scripts/verify_core.py
python3 scripts/verify_array.py
python3 scripts/moment_certificate.py
printf 'PASS_PYTHON_PREFLIGHT_ONLY (not Lean verification)\n'
python3 scripts/construct_native.py
python3 scripts/verify_finite.py
python3 -O scripts/verify_finite.py
python3 scripts/generate_analytic.py
