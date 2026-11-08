#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
python3 scripts/audit_axioms.py
echo 'PASS_LOCAL_LEAN_CHECKS: final exact-DFT theorem requires scripts/check_final.sh and official verification'
