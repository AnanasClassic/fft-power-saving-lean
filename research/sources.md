# Pinned sources and attribution

Sources were resolved on 8 November 2026. The authoritative machine-readable
hash list is `certificates/source_pins.json`. Upstream material is not claimed
as new work. A local reproduction is not independent human review.

## Trusted model and verifier

- [Big O Speedrun verifier](https://github.com/bigospeedrun/verifier/tree/195060b222d63c2a22cf8f5dd390f34e9b446323),
  commit `195060b222d63c2a22cf8f5dd390f34e9b446323`. Read README, target guide,
  direct-submission instructions, execution guide and relevant staging,
  target generation, allowed-axiom and Comparator/nanoda source.
- The unchanged `DFTProgram` definitions come from that revision's
  [trusted challenge](https://github.com/bigospeedrun/verifier/blob/195060b222d63c2a22cf8f5dd390f34e9b446323/challenges/dft/UniformFourier233.lean).
  Only its two final challenge placeholder theorems are excluded locally;
  every preceding definition is retained byte for byte. This is not a proof
  that the final Comparator passes.
- The challenge credits the original [OpenAI model](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb),
  commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, Apache-2.0.
- Current [OpenAI math source](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae)
  was separately resolved to `4eaee87548250b2682affda7d05d947c05554bae`.
  The initial package's OpenAI revision string differs; the resolved revision
  is recorded rather than silently relying on that string.
- Lean `leanprover/lean4:v4.34.1`, compiler commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (local Darwin arm64 release).
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612),
  commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, with all transitive pins
  copied from the verifier's `profiles/lake-manifest.json`.
- Comparator, lean4export and nanoda pins are preserved in
  `research/upstream/profiles/tools.json`. Those tools have not been run on
  a final theorem in this project.

## Formal engines and preceding DFT work

- [Halit Ziya KARTAL's v6 submission](https://github.com/bigospeedrun/verifier/tree/195060b222d63c2a22cf8f5dd390f34e9b446323/submissions/dft/halitziyakartal-halitziyav6-pi).
  Read the preserved source headers, forward-only supplier interface,
  controller, tensor-engine interface, rate certificate and Fourier seam.
  The generic `Work/BlockAccounting/Moment.lean`, `Sharp.lean` and
  `Work/TensorProto/Strictify.lean` are copied byte for byte from this pinned
  tree, with their attribution comments intact. The subsequent native supplier
  integration imports the exact 326-module dependency closure listed in
  `native_dependency_closure.json`, including the inherited OpenAI Fourier
  reduction and the KLW sound checker. Each copied file is separately hashed
  in `certificates/source_pins.json`; all original headers are retained.
- [Jacob Sussman's lever submission](https://github.com/bigospeedrun/verifier/tree/195060b222d63c2a22cf8f5dd390f34e9b446323/submissions/dft/jacobalansussman-lever-2979-full-cut).
  Sussman supplies the formal engines, mixed live-kernel recursion, tensor
  product/strictification infrastructure and inherited reduction integration.
  OpenAI supplies the original model and all-length Fourier reduction.
- The `ofHist` lemmas and tail-budget proof pattern in the new analytic
  certificate are adapted from Kartal's `Work/BQT/RateBQT772.lean`; they are
  explicitly credited in the source. New work proves the proposed stronger
  histogram's analytic inequalities; it does not claim the inherited engines.
- [Ryan Shea's Fourier repository](https://github.com/shea256/fourier-transform-below-nlogn/tree/0e61af6ce0ef712494c93c902baefa314ef7e23c),
  commit `0e61af6ce0ef712494c93c902baefa314ef7e23c`. Its README, manuscript context
  and attribution distinguish finite circuit evidence from the full exact DFT
  transfer and retain community construction/engine credits. No proof modules
  from this repository are copied into the current build.

## Native word, local edits and controller

- [CrocSwap baseline](https://github.com/CrocSwap/integer-mult-bounds/tree/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/p104-owned772-relay-descent),
  commit `7c49fe32c55de02c2c873655c804b16e4c3fef0a`. CubeJerry / Jerry Chen's
  owned772 word and its predecessor chain retain their source notices.
  Baseline decompressed payload SHA256:
  `44e8ef6bfd6fd0aae5252861534b968f241f3f48b7f9266be2e981bf84a219a8`.
- [DreamingOfClouds PR6144](https://github.com/CrocSwap/integer-mult-bounds/pull/6144),
  source revision `5ec9b6dafc1ec54e2c0ca0771e8ed032f7888417`:
  helper 732's read moved to frame 117, and earlier relay-descent work.
- [Ali Romman PR6167](https://github.com/CrocSwap/integer-mult-bounds/pull/6167),
  source revision `564a076b113621a93edc4e39968ee4e4a8c9caf0`:
  retained operand for reader 451, removing a root stop. The current
  reconstruction uses an unused lifetime of register 794 instead of the
  original revision's register 770. Ali Romman's OpenAI Codex assistance and
  DreamingOfClouds' Claude assistance remain credited upstream.
- [DreamingOfClouds PR6833](https://github.com/CrocSwap/integer-mult-bounds/pull/6833),
  source revision `51f54e3c31f2f3a3e056a483b3ed66ae916ad06a`:
  the 9+9 chain-nested controller, its integral basis changes and common whole
  idles. `CALLER.json`, its proof/adapters, LICENSE/NOTICE and independent root
  audit are retained. Raw event-list SHA256:
  `03ecddfd75d0dbe325fcc489a50ae7657364482f0d887d81fa131ff6bf41fe70`.
- Cinna Davis supplies the thin-query/query-thinned controller lineage.
  Ali Romman, thu-nmrc, zxv, DreamingOfClouds, CubeJerry and the predecessors
  named in the retained notices supply the circuit/controller improvements.
  Douglas Colkitt's source-payload/portability methods are credited in the
  retained native validator. The original independent validator is preserved;
  its adapted copy only parameterizes the owned-occupancy cap for this witness.

## Current integration and claim limits

The new reconstruction scripts, rational paired-controller replay, Lean array
and inverse-query identities, real moment enclosure certificate, parameter
instantiation, project packaging and audit are prepared for this research
request with OpenAI Codex assistance. The initial local package's author is
not inferred from its presence in Downloads. No inherited work is rebranded.

The board was inspected for overlapping results. The inspected page listed
Kartal's π-related result as Lean Verified and a higher `0.0031484962` refile
as Claimed. This is a dated observation, not a current-record guarantee; the
record must be checked again before any submission. The new target being
numerically larger does not establish novelty, priority, authorship, practical
speed or verified-record status.

Root LICENSE is the inherited Apache-2.0 license; relevant upstream notices
are retained in source headers, `research/NOTICE.verifier` and vendor notices.
