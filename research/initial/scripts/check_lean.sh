#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake/Lean 4 is not installed. Lean build has NOT passed.' >&2
  exit 127
fi
lake update
lake build
printf 'PASS_LEAN_MODULE_BUILD (not the missing exact-DFT theorem)\n'
