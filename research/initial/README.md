# Exact-DFT two-chain bound: Lean formalization work package

**Status: in progress. This is NOT an end-to-end Lean proof, and does not
establish a Lean-verified FFT record.**

Target theorem (not proved in this package): exact DFT in the original exact
complex arithmetic RAM model with

\[
T(n)=O\bigl(n(\log n)^{1-3363623/10^9}\bigr).
\]

This package is a new formalization of critical *local proof obligations* from
the 8 November 2026 `fft-delta-0.003363623.pdf` research note. The PDF and the
research source ZIP exist in the owner's ChatGPT file library. The source ZIP
could not be mounted into the local code execution runtime in this turn, so
the 22,836-event word and 2,598-event caller have **not** been imported into
Lean here. No remote GitHub repository was created or modified.

## Files

| File | What it formalizes | Present verification |
|---|---|---|
| `FFTChainDFT/Normalizer.lean` | Abstract paired normalizer, `Λ²=P`, `(ΛQ)²=I` | Lean proof source, **not compiled** |
| `FFTChainDFT/ArrayNormalizer.lean` | Whole-array rational gates for any index type and involutive address shift | Lean proof source, **not compiled** |
| `FFTChainDFT/TransportedQuery.lean` | `(ΛQ)²=I` for any complex-linear `Q` with `Q²=P` on two arbitrary arrays | Lean proof source, **not compiled** |
| `FFTChainDFT/Inventory.lean` | Native + controller histogram reconstruction, number of fields and total charged rank | Kernel-oriented `decide` proofs, **not compiled** |
| `FFTChainDFT/Parameters.lean` | Rational gaps and finite tensor-tail power inequalities | Lean `norm_num` proofs, **not compiled** |
| `FFTChainDFT/MomentReceipt.lean` | Rational endpoint comparisons from the external moment receipt | Lean `norm_num` proofs, **not compiled** |
| `scripts/moment_certificate.py` | Strict rational moment bounds using proved analytic remainder formulas | **Executed successfully** (CPython) |
| `scripts/verify_core.py` | Independent polynomial-ring and integer checks | **Executed successfully** (CPython) |
| `scripts/verify_array.py` | Exact Gaussian-rational basis check of whole-array normalizer | **Executed successfully** (CPython) |

**No `sorry`/`admit`/user axioms appear as proof placeholders.** This does not
mean compilation succeeds; it has **not** been run, because neither `lean`
nor `lake` is installed in the current execution environment and network
access for installing them is disabled.

## Local reproduction

Python 3.10+ and the standard library suffice for preflight:

```bash
python3 scripts/generate_inventory.py
python3 scripts/verify_core.py
python3 scripts/verify_array.py
python3 scripts/moment_certificate.py
```

Once Lean 4 and Mathlib are available (the TOML pins a provisional compatible
version, not necessarily the upstream verifier's toolchain):

```bash
lake update
lake build
```

The package deliberately does **not** print `Lean verified` until `lake build`
actually succeeds and the final target theorem is added. If an upstream Lean
project is to be reused, replace the provisional `lean-toolchain` with the
exact toolchain from the pinned upstream proof first.

## Recomputed finite numerical data

The *full*, doubled physical histograms give exactly:

- Productive fields: **24,392**.
- Paid calls: **128,116**.
- Productive rank mass: **336,224**.
- Paid rank mass: **334,704**.
- Maximum paid rank: 64; maximum target rank: 145.
- Finite saving: `C=420453/125000000=0.003363624`.
- Engine saving: `eta=6727247/2000000000=0.0033636235`.
- Target DFT saving: `delta=3363623/1000000000=0.003363623`.

The raw full-histogram moment margin at `1-C` is rigorously bracketed by
`51611111215192/10^18` and `51611111215193/10^18`. This is twice the
half-inventory margin in the reference note. See `moment_receipt.json` for the
exact ratio enclosures and `scripts/moment_certificate.py` for a transparent
rational series proof of the enclosures; the series proof has **not** yet been
translated into Lean.

## What remains before an FFT theorem is proved in Lean

See [OPEN_OBLIGATIONS.md](OPEN_OBLIGATIONS.md) for exact proof targets and the
pin-specific integration path. The most important missing theorem is a
`GLiveKernelM` certificate for the **actual modified owned772 word and 9|9
caller**, with full arbitrary-input and dirty-helper semantics. A moment
inequality alone is not an operator proof. The final theorem also requires
re-instantiating the all-length Fourier compiler at the new exponent and
checking its original RAM statement/axioms.

## Sources and attribution

This is based on OpenAI's exact-DFT framework and the formally checked public
work of Jacob Sussman and Halit Ziya Kartal. The native word is credited to
CubeJerry and the P104 predecessor chain; the 9|9 controller is credited to
DreamingOfClouds (PR6833). The two schedule edits are credited to
DreamingOfClouds (PR6144) and Ali Romman (PR6167). See
[PROVENANCE.md](PROVENANCE.md). None of their work is claimed as new here.
