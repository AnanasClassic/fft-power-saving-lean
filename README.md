# Exact DFT power saving in Lean 4

The project proves the exact saving **δ = 3363623/1000000000** in the original
`OAI.PowerSaving.DFTProgram` model. The exported theorem is `Race.bound` in
`Submission/Chain/Bound.lean`; the root `Submission.lean` imports it.

**Acceptance evidence:** [CI d48314b](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42531587924) accepted the root, exact statement and four-theorem axiom audit. This repository is private and has no
public Big O Speedrun `Lean Verified` status. A private preflight with the
unchanged official checker is separate from an authorized public submission.

## What the proof contains

- A concrete modified 22,836-event owned772 supplier, checked through the
  inherited sound KLW/native-circuit machinery on arbitrary valid inputs.
- A literal 2,598-instruction paired 9+9 controller on forty independent main
  roles, with thirty-six native helper banks and explicit query scratch.
- Actual proper GWords for the rational two-array normalizer, queries, native
  calls, adapters and final phase corrections; the concrete `GLiveKernelM`.
- Both complete physical histograms, with 24,392 productive targets and 128,116
  paid calls per gauge, and rank masses 336,224 and 334,704 respectively.
- Real moment bounds at C=0.003363624, tensor degree 12,800, cutoff 12^12800 and
  completion floor 13^12800, then the new tensor engine at η=0.0033636235.
- The inherited all-length Fourier reduction re-instantiated with that engine:
  root selection, scalar preparation, integer/address work, storage and the
  exact δ bound. No previous weaker final theorem supplies `Race.bound`.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Python replay
and generated numeric certificates are supporting reproducibility checks, not
premises substituted for physical correctness or Lean proofs.

## Reproduce on CI

All ongoing builds run on GitHub Actions; the Mac's local build cache is absent.
The manual incremental workflow checks changed source/dependency closures. The
full workflow runs Python reproduction, source guards, **`lake build`**, the
exact statement check and axiom audits. The private preflight pins Comparator and nanoda to the official verifier
revision. It initializes the audit worker setting in the generated runner
entrypoint and reserves disk space for replay on the hosted VM. See the
[research log](research/log.md) for the acceptance evidence and runner fixes.

Lean: `leanprover/lean4:v4.34.1`. Mathlib:
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The manifest and `autoImplicit=false`
match the official DFT profile. There are no custom Lake hooks or additional
proof dependencies. On a suitably provisioned build machine:

```bash
lake exe cache get                 # dependency setup, before offline proof checking
lake build
bash scripts/check_final.sh
python3 scripts/audit_axioms.py --file Submission/FinalAudit.lean \
  --receipt certificates/final_axioms.json --scope "complete exact DFT proof"
```

The official verifier stages only regular `Submission.lean` and
`Submission/**/*.lean` sources. It supplies its own Lake files, pinned
Mathlib/toolchain and trusted target; it does not run this repository's scripts
or download proof data during the sandboxed check.

## Attribution and scope

OpenAI supplies the computational model and all-length Fourier reduction.
Jacob Sussman supplies the engines, tensor/live-kernel machinery and reduction
integration. Halit Ziya KARTAL supplies the preceding Lean instantiations.
DreamingOfClouds supplies the two-chain controller and earlier circuit work;
Ali Romman supplies circuit/controller optimizations. CubeJerry/Jerry Chen,
Cinna Davis and the other contributors in retained notices supply inherited
constructions and certificates. See [the pinned source report](research/sources.md).
This integration and its verification do not establish novelty or priority.

The three named original ZIP/PDF attachments were unavailable. The extracted
package is preserved in `research/initial/`. The explicitly reconstructed native
payload has SHA256
`29c8938138476b02cfc5977558f5065953c56f7a91926bc0e5de1fcbffecd3e1`, different
from the digest quoted in the unavailable note. The proof establishes this
reconstruction, not recovery of that archive.

See [the proof map](research/proof.md), [verification audit](research/audit.md),
[pinned sources and credits](research/sources.md), and [research log](research/log.md).
No issue, PR, public repository or record announcement has been authorized.
