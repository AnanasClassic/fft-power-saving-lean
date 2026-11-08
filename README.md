# Exact DFT power saving in Lean 4

**Research checkpoint. The requested `Race.bound` at saving
`3363623/1000000000` is not proved. This is not a competition-ready submission
and has no official Lean Verified status.**

Local project: `/Users/vlad/projects/fft-power-saving-lean`.
Private remote: <https://github.com/AnanasClassic/fft-power-saving-lean>.

The work starts from the uncompiled `fft-chain-lean` package found in Downloads.
The three named research archives/PDF were not available in this session. The
original extracted package is retained under `research/initial/`; its obsolete
build/status statements are historical, not current instructions.

## What is implemented and checked locally

- Universal two-array normalizer identities on arbitrary complex arrays,
  including the actual inverse query obtained as the cube of the query.
- Integer histogram formulas, counts 24,392 / 128,116, rank masses
  336,224 / 334,704, and rank support bounds.
- A real analytic proof of the finite moment saving at
  `C = 420453/125000000 = 0.003363624`, not just a rational receipt.
- Three real moment ratio bounds and Sussman's inventory-level strictification
  at tensor power 12,800, paid cutoff `12^12800`, and floor `13^12800`.
- A reconstructed 22,836-event native word, exact sparse Python replay on
  799 independent formal-coordinate inputs, and a 2,598-event rational paired
  controller replay on 40 independent roles. These replays are **not Lean
  proofs of native/physical semantics**.
- Axiom audits of the local Lean theorems, restricted to `propext`,
  `Classical.choice`, and `Quot.sound`.

The reconstructed native payload has SHA256
`29c8938138476b02cfc5977558f5065953c56f7a91926bc0e5de1fcbffecd3e1`.
It does **not** match the research note's reported digest. It is an explicitly
identified reconstruction, not a purported recovery of the missing archive.

## Reproduce

Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
`lake-manifest.json` is copied from the pinned official verifier; local options
also use its `autoImplicit = false` setting.

```bash
bash scripts/check_python.sh
lake exe cache get                 # online setup only
bash scripts/check_lean.sh         # build and local theorem axiom audit
python3 scripts/source_guard.py
bash scripts/check_final.sh        # currently FAILS: Race.bound is absent
```

After dependency setup, `lake build` does not need a network fetch. All proof
modules are under `Submission/`; there are no custom Lake build hooks or new
proof dependencies beyond the official Mathlib pin. The official checker
ignores the submitted Lake files and scripts.

`Submission/Target.lean` specifies the requested proposition using an unchanged
prefix of the trusted model. It is a definition of the goal, not a theorem.
`Submission.lean` imports only completed local results. A placeholder proof,
extra axiom, weaker final theorem, or invented `Race.bound` is not supplied.

## Verification status

| Stage | Status |
|---|---|
| Python certificates | Passed locally, including finite replay and rejection controls |
| Lean source elaboration | Passed for the completed local modules |
| Lean kernel | Accepted the local theorem proofs; final DFT theorem absent |
| Axiom audit | Passed for local theorems; final DFT theorem not audited |
| Official Comparator | Not run; final theorem absent |
| Official Lean Verified | Not obtained |
| Nanoda | Not run |

GitHub Actions reproduces the research checks on every push. Its final theorem
gate intentionally fails until the exact `Race.bound` exists. A successful
local lemma build is not a passing competition submission.

See [the mathematical note](research/proof.md), [audit and obligations](research/audit.md),
[pinned sources and attribution](research/sources.md), and [research log](research/log.md).
The recorded Git commit is a research checkpoint, not a submission SHA.

No issue, pull request, public repository, or record announcement is authorized
or created by this checkpoint. Public submission requires completion of the
proof and the user's explicit authorization.
