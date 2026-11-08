import Mathlib

/-!
# Exact comparisons for a rational interval receipt

The numerators come from `scripts/moment_certificate.py` (grid 10^18).
This module checks only inequalities *between rational endpoints*.
It does not yet prove the analytic inclusion of the true real moments in these
intervals. That proof requires formalized log/exp Taylor remainder bounds.
-/

namespace FFTChainDFT
namespace MomentReceipt

private def grid : ℚ := 1000000000000000000

/-- Lower and upper outward bounds on `M_(1-C)(T)-M_(1-C)(P)`. -/
def marginLower : ℚ := 51611111215192 / grid
def marginUpper : ℚ := 51611111215193 / grid

/-- Outward rational bounds on the three strictification ratios. -/
def alphaUpper : ℚ := 999999999844864783 / grid
def gammaUpper : ℚ := 997695769675528001 / grid
def completionUpper : ℚ := 945209312649479023 / grid

/-- The proposed *rational* enclosure has nonzero width and positive margin. -/
theorem margin_endpoints : 0 < marginLower ∧ marginLower < marginUpper := by
  norm_num [marginLower, marginUpper, grid]

/-- If the analytic enclosure is proved, this is the required alpha bound. -/
theorem alpha_numerical_cap : alphaUpper < 1 - 1 / 10000000000 := by
  norm_num [alphaUpper, grid]

/-- If the analytic enclosure is proved, these are the charged tail caps. -/
theorem gamma_numerical_cap : gammaUpper < 499 / 500 := by
  norm_num [gammaUpper, grid]

theorem completion_numerical_cap : completionUpper < 19 / 20 := by
  norm_num [completionUpper, grid]

end MomentReceipt
end FFTChainDFT
