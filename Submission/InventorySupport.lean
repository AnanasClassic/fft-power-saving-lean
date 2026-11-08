import Submission.Inventory
import Submission.MomentAnalytic

namespace FFTChainDFT.Inventory

theorem paid_rank_bounds {r : ℕ} (h : paidCount r ≠ 0) : 1 ≤ r ∧ r ≤ 64 := by
  unfold paidCount at h
  split at h <;> omega

theorem target_rank_bounds {r : ℕ} (h : targetCount r ≠ 0) : 1 ≤ r ∧ r ≤ 145 := by
  unfold targetCount at h
  split at h <;> omega

end FFTChainDFT.Inventory

namespace FFTChainDFT.Analytic

theorem exponent_separation :
    0 < 1-C ∧
    1-C < 1-(6727247 : ℝ)/2000000000 ∧
    1-(6727247 : ℝ)/2000000000 < 1-(3363623 : ℝ)/1000000000 ∧
    1-(3363623 : ℝ)/1000000000 < 1 := by
  norm_num [C]

end FFTChainDFT.Analytic
