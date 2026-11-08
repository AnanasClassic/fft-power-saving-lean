# Verification audit and remaining obligations

Date: 9 November 2026 (Moscow). This is an evidence report, not a public
competition verification receipt or a novelty claim.

## Separate evidence levels

| Stage | Evidence and status |
|---|---|
| Python certificates | Earlier inventory, sparse native/controller replay and rational certificates passed; full CI reproduction is part of the normal build workflow. |
| Lean source elaboration | [CI d48314b](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42531587924) accepted the root, exact statement and four-theorem axiom audit |
| Lean kernel | The concrete live word, complete finite witness, tensor engine, all-length reduction and exact `Race.bound` were accepted in the root CI check. |
| Axiom audit | `Submission/FinalAudit.lean` checks `wordCert`, `rawCert_exists`, `FFTChainDFT.engine`, and `Race.bound`; only `propext`, `Classical.choice`, `Quot.sound` are permitted. See the associated CI artifact. |
| Full `lake build` | CI run [42531656698](https://github.com/AnanasClassic/fft-power-saving-lean/actions/runs/42531656698), tracked independently from the incremental source check. Consult that run's conclusion. |
| Official Comparator profile | Private test-only workflow prepared at the unchanged official verifier pin; its receipt must be inspected separately. A source/type check is not Comparator acceptance. |
| Nanoda | Separate replay in that private workflow; no pass is inferred from Lean acceptance. |
| Public `Lean Verified` status | Not obtained. Repository private; no issue or PR submitted. |

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

## Remaining verification and publication obligations

1. Complete the ordinary CI build and inspect every required check, including
   deterministic source generation and actual final axiom output.
2. Complete the private unchanged official Comparator run on an immutable source
   commit. Preserve its exact challenge, tool/source pins, axiom result and
   per-kernel status. A resource-limited or ambiguous nanoda result must remain
   distinguished from acceptance or rejection.
3. Prepare the source-only package and exact full SHA using those receipts.
   Keep all inherited attribution, original notices and licenses.
4. Before any public submission, recheck the competition's current profile and
   record gate and obtain the user's explicit authorization to publish the
   repository and submit an issue. No private CI receipt grants the public
   leaderboard label, mathematical novelty, priority or authorship.
5. Reconcile the original archive digest only if that archive becomes available;
   this provenance limitation is independent of the proved reconstruction.

All continuation builds run on GitHub Actions. Local task build objects and
large temporary downloads were removed; they are not prerequisites of the
source-only submission. The official proof run uses only staged Lean sources
and its own allowed dependencies, with no repository Lake hooks or proof-data
network downloads.
