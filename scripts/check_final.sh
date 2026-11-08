#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
task_check_dir="$(mktemp -d)"
trap 'rm -rf "$task_check_dir"' EXIT
cat > "$task_check_dir/FinalCheck.lean" <<'LEAN'
import Submission
open OAI.PowerSaving Filter Asymptotics
example : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (3363623 : ℝ)/1000000000)) := Race.bound
#print axioms Race.bound
LEAN
lake env lean "$task_check_dir/FinalCheck.lean"
echo 'LOCAL_FINAL_TARGET_ELABORATED: official Comparator/nanoda still required'
