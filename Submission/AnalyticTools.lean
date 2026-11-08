import Submission.Work.BlockAccounting.Moment
import Submission.Work.BlockAccounting.Sharp

/-!
Rational enclosures of real powers. The log certificates use the exponential
series lemmas inherited from Jacob Sussman's and Halit Ziya Kartal's submissions.
The bounds below are kernel proofs; certificate generation is not trusted.
-/

namespace FFTChainDFT.Analytic
open Finset

noncomputable def expLower (x : ℝ) : ℝ :=
  ∑ i ∈ range 8, x ^ i / (i.factorial : ℝ)

noncomputable def expUpper (x : ℝ) : ℝ :=
  expLower x + x ^ 8 * 9 / ((Nat.factorial 8 : ℝ) * 8)

theorem expLower_le (x : ℝ) (hx : 0 ≤ x) : expLower x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx 8

theorem le_expUpper (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ expUpper x := by
  have h := Real.exp_bound' h0 h1 (n := 8) (by norm_num)
  norm_num only [Nat.cast_ofNat, show (8 : ℝ) + 1 = 9 by norm_num] at h
  convert h using 1 <;> norm_num [expUpper, expLower]

/-- A certificate consists entirely of rational comparisons and two log bounds. -/
theorem rpow_enclosure (r C L U lo hi : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hsmall : C * U ≤ 1)
    (hl : L ≤ Real.log r) (hu : Real.log r ≤ U)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hnumlo : lo * expUpper (C * U) ≤ r)
    (hnumhi : r ≤ hi * expLower (C * L)) :
    lo ≤ r ^ (1 - C) ∧ r ^ (1 - C) ≤ hi := by
  have hEL : expLower (C * L) ≤ Real.exp (C * Real.log r) :=
    (expLower_le _ (mul_nonneg hC hL)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hC))
  have hEU : Real.exp (C * Real.log r) ≤ expUpper (C * U) :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hC)).trans
      (le_expUpper _ (mul_nonneg hC hU) hsmall)
  have heq : r ^ (1 - C) = r / Real.exp (C * Real.log r) := by
    rw [Real.rpow_def_of_pos hr, mul_sub, mul_one, Real.exp_sub, Real.exp_log hr,
      mul_comm (Real.log r) C]
  constructor
  · rw [heq, le_div_iff₀ (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hEU hlo).trans hnumlo
  · rw [heq, div_le_iff₀ (Real.exp_pos _)]
    exact hnumhi.trans (mul_le_mul_of_nonneg_left hEL hhi)

end FFTChainDFT.Analytic
