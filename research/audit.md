# Verification audit and remaining obligations

Date: 9 November 2026 (Moscow). This is an evidence report, not a public
competition verification receipt or a novelty claim.

## Separate evidence levels

| Stage | Evidence and status |
|---|---|
| Python certificates | Passed in the [full CI run](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42532864715), including rejection controls and deterministic generation. |
| Lean source elaboration | Passed for the complete exact `Race.bound` source closure. [Root CI](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42531587924). |
| Lean kernel | Accepted the concrete live word, finite witness, tensor engine, all-length reduction and exact bound. [Root CI](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42531587924). |
| Axiom audit | The full CI audit and the independent test-only verifier audit passed. `Race.bound` uses only `propext`, `Classical.choice`, and `Quot.sound`. [Full CI](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42532864715), [verifier rerun](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42547883869). |
| Full `lake build` | Passed on `38d22084f270723dbe769b94bd690c372a08e390`. [Full CI](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42532864715). |
| Official Comparator | Accepted the exact claim at the pinned verifier revision in the [initial test-only run](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42532755546) and the [rerun](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42547883869). |
| Nanoda | Passed independently in the [test-only rerun](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42547883869). |
| Public `Lean Verified` status | Pending a separate competition submission and verification. |

`certificates/ci_live_kernel.json` binds the first accepted concrete live word to
its source commit and SHA256. That earlier CI run failed in the downstream
count module: it is evidence for the live word, not for that entire run.
Historical receipts keep their stated scopes; they are not retroactively
relabelled as final-theorem audits.

## Closed mathematical obligations

- **Native supplier:** actual modified owned772 certificate, frame/label/scalar
  validity, all-width supplier contract, native paid profile, helper residuals
  and all helper ranks. The modified word rejoins the baseline after two
  locally changed chunks.
- **Physical normalizer and queries:** actual proper GWords and arbitrary-data
  actions, including Λ²=P I₂ and (ΛQ⁻¹)²=I₂, and exact recursive costs.
- **Controller and live kernel:** all 2,598 literal operations, arbitrary-data
  main and helper endpoints, thirty-six distinct banks called once, actual
  adapters, scratch overwrite and final phase corrections. No zero-helper
  assumption replaces arbitrary live helper inputs.
- **Complete cost/targets:** the word price holds for every price list; indicator
  prices yield its histogram for all natural ranks. Actual live-role counts
  yield the productive histogram, including every bank and both arrays.
- **Tensor improvement:** dimension 145, target/rank validity, real moment
  saving at C=0.003363624, degree 12,800, cutoffs 12^v and 13^v, floor
  attainment and the new mixed tensor engine at η=0.0033636235.
- **Fourier reduction:** the new engine feeds the full inherited all-length
  reduction. The exact δ=0.003363623 theorem retains root selection, scalar
  preparation, integer/address work, memory and operation accounting from the
  original `DFTProgram` model.

The final export does not use a previously proved weaker final DFT theorem.
`Submission/Target.lean` uses the actual owning OpenAI Goal module, whose
trusted definitions are preserved. Text/pin comparison is supporting evidence;
the official Comparator additionally checks relevant definitions and terms.

## Source availability and reconstruction

The named `FFT_Lean_Formalization_2026-11-08.zip`,
`fft-delta-0.003363623.zip`, and `fft-delta-0.003363623.pdf` were unavailable.
The extracted Downloads package's 21 files were inventoried and preserved in
`research/initial/`. The unavailable PDF is not asserted to have been read.

The quoted digest was
`7397ed2a343b3229295507741c67dce259f976cefad067eb3e0503bf6230fc94`.
The explicitly reconstructed native word instead has digest
`29c8938138476b02cfc5977558f5065953c56f7a91926bc0e5de1fcbffecd3e1`.
Its behavior and counts are established by this formalization. It is a proved
alternative at the target bound, not an assertion of byte identity to the
missing archive. The paired controller is also an explicitly documented
lowering of the pinned raw caller.

## Test-only verification and publication

The verified source commit is `38d22084f270723dbe769b94bd690c372a08e390`. The verifier revision is
`e4195cbf8c813772227a5fe4fd21c03c0a1a4fa4`. The initial test-only run accepted the Lean proof in Comparator.
Its separate axiom audit stopped at an uninitialized `threads` variable and
nanoda could not start with the disk space available on the CI runner.
The rerun used the same proof files, target, checker binaries and sandbox.
It initialized `threads` in the generated audit entrypoint and reclaimed space
on the temporary runner. Comparator, the independent axiom audit and nanoda
all passed. [Initial run](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42532755546), [rerun](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42547883869), [upstream issue](https://github.com/bigospeedrun/verifier/issues/188).

The public competition submission remains a separate step. The exact tested
commit and claim are in [submission-metadata.txt](../submission-metadata.txt).
The official verifier stages the allowed Lean sources and supplies its own
trusted dependencies. The unavailable source archive still limits provenance
for the reconstructed native word.
