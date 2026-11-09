# Research towards delta = 0.005

Separate experimental branch, based on the submitted proof commit 38d22084f270723dbe769b94bd690c372a08e390. The main branch and Big O Speedrun submission are unchanged.

No new DFT bound is claimed. The bounded workflow on this research branch replaces the full Lean build with a finite research probe. Its green status is NOT a Lean verification.

The input word/caller is DreamingOfClouds PR6934, pinned at 4e13b7acdbea1c9f12aa88126435360eecea7401. It inherits the authors and obligations documented in that PR. Helper splitting is Ali Romman's PR5599 mechanism. The new probe searches complete same-frame nullspaces over a finite field, then verifies each exported candidate over the rationals without a restricted denominator alphabet. A modular candidate is not a certificate.

The goal is an exact-complex DFT construction, not a claim about integer multiplication. Existing finite replays do not establish the all-width physical interface or the final DFT reduction. All such obligations remain explicit.
