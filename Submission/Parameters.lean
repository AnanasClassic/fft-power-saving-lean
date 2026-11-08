import Mathlib

/-!
# Exact rational parameter choices

These are parameters occurring in the proposed asymptotic transfer. The
arithmetic theorem below does NOT establish the finite moment inequality or
an exact FFT program; those are separate, still-open formalization obligations.
-/

set_option exponentiation.threshold 16000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FFTChainDFT

/-- Finite-moment saving from the research note. -/
def finiteSaving : ℚ := 420453 / 125000000
/-- Tensor-engine target saving. -/
def engineSaving : ℚ := 6727247 / 2000000000
/-- Claimed Fourier saving. -/
def fourierSaving : ℚ := 3363623 / 1000000000

/-- Both absorption gaps are strictly positive and equal to `1/2·10⁻⁹`. -/
theorem saving_gap_exact :
    finiteSaving - engineSaving = 1 / 2000000000 ∧
    engineSaving - fourierSaving = 1 / 2000000000 := by
  constructor <;> norm_num [finiteSaving, engineSaving, fourierSaving]

/-- Verifiable numerical separation of the three stages. -/
theorem saving_order :
    0 < fourierSaving ∧
    fourierSaving < engineSaving ∧
    engineSaving < finiteSaving ∧
    finiteSaving < 1 := by
  norm_num [finiteSaving, engineSaving, fourierSaving]

/-- The auxiliary rational upper bound used for the tensor-tail budget. -/
theorem rational_tail_budget :
    (1 : ℚ) / (1 + 12800 / 10000000000) +
      2 / (2 : ℚ) ^ 32 + 2 / (2 : ℚ) ^ 160 < 1 := by
  norm_num

/-- Exact power comparison cited in the rational strictification. -/
theorem first_tail_400 : 2 * (499 : ℕ) ^ 400 < 500 ^ 400 := by
  norm_num

/-- Exact power comparison cited in the rational strictification. -/
theorem second_tail_80 : 2 * (19 : ℕ) ^ 80 < 20 ^ 80 := by
  norm_num

end FFTChainDFT
