import Submission.MomentAnalytic

/-!
Inventory-level strictification at the exact proposed parameters.
The proof follows the method of Kartal's RateBQT772.lean and Sussman's
TensorProto.Strictify. It does not assert a finite-circuit contract.
-/
set_option exponentiation.threshold 16000
set_option maxRecDepth 16000

namespace FFTChainDFT.Analytic
open TensorProto
noncomputable section

/-- Bernoulli estimate, inherited from Kartal's certificate. -/
lemma bernoulli_inv (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (v : ℕ) :
    (1 - ε)^v ≤ 1 / (1 + v*ε) := by
  have hpos : 0 < 1 + (v : ℝ)*ε := by positivity
  rw [le_div_iff₀ hpos]
  have hb : 1 + (v : ℝ)*ε ≤ (1+ε)^v := one_add_mul_le_pow (by linarith) v
  have h2 : (1-ε)^v * (1+ε)^v ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) v)).trans h2

theorem tensor_tail_budget :
    (1 - (1 : ℝ)/10000000000)^12800 +
      2*(499/500 : ℝ)^12800 + 2*(19/20 : ℝ)^12800 ≤ 1 := by
  have h1 := bernoulli_inv ((1 : ℝ)/10000000000) (by norm_num) (by norm_num) 12800
  have h2a : (499/500 : ℝ)^400 ≤ 1/2 := by norm_num
  have h2 : (499/500 : ℝ)^12800 ≤ (1/2 : ℝ)^32 := by
    rw [show (12800 : ℕ) = 400*32 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2a 32
  have h3a : (19/20 : ℝ)^80 ≤ 1/2 := by norm_num
  have h3 : (19/20 : ℝ)^12800 ≤ (1/2 : ℝ)^160 := by
    rw [show (12800 : ℕ) = 80*160 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h3a 160
  have h4 : (1 : ℝ)/(1+((12800 : ℕ) : ℝ)*((1 : ℝ)/10000000000)) +
      2*(1/2 : ℝ)^32 + 2*(1/2 : ℝ)^160 ≤ 1 := by norm_num
  generalize (1-(1 : ℝ)/10000000000)^12800 = A at h1 ⊢
  generalize (499/500 : ℝ)^12800 = G at h2 ⊢
  generalize (19/20 : ℝ)^12800 = D at h3 ⊢
  generalize (1/2 : ℝ)^32 = H1 at h2 h4
  generalize (1/2 : ℝ)^160 = H2 at h3 h4
  generalize (1 : ℝ)/(1+((12800 : ℕ) : ℝ)*((1 : ℝ)/10000000000)) = B at h1 h4
  linarith

lemma tail_combine {x y z : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1-(1 : ℝ)/10000000000) (hy0 : 0 ≤ y) (hy : y ≤ 499/500)
    (hz0 : 0 ≤ z) (hz : z ≤ 19/20) :
    x^12800 + 2*y^12800 + 2*z^12800 ≤ 1 := by
  have h1 := pow_le_pow_left₀ hx0 hx 12800
  have h2 := pow_le_pow_left₀ hy0 hy 12800
  have h3 := pow_le_pow_left₀ hz0 hz 12800
  have h4 := tensor_tail_budget
  generalize (1-(1 : ℝ)/10000000000)^12800 = A at h1 h4
  generalize (499/500 : ℝ)^12800 = G at h2 h4
  generalize (19/20 : ℝ)^12800 = D at h3 h4
  linarith

/-- The actual real-moment strictification inequality, not a rational receipt. -/
theorem strictified_moment :
    mom (1-C) (strictP (ofHist targetHist) (ofHist paidHist) 12800
      (12^12800) (13^12800)) ≤
    mom (1-C) (strictT (ofHist targetHist) 12800 (13^12800)) := by
  have hT := target_pos
  have hc : (0 : ℝ) < (12 : ℝ)^C := Real.rpow_pos_of_pos (by norm_num) _
  have hden : (0 : ℝ) < (12 : ℝ)^C * mom (1-C) (ofHist targetHist) := mul_pos hc hT
  apply strictify (c := 12) (b := 13) (t := 1-C) (u := C)
    (by norm_num [C]) (by norm_num [C]) (by norm_num [C])
    (by norm_num [C]) (by norm_num [C]) hT
  simp only [Nat.cast_ofNat]
  apply tail_combine
  · exact div_nonneg (mom_nonneg _ _) hT.le
  · rw [div_le_iff₀ hT]; exact alpha
  · exact div_nonneg (mom_nonneg _ _) hden.le
  · rw [div_le_iff₀ hden, show (1 : ℝ)-C+C = 1 by ring, paid_mass]
    exact gamma
  · have hc' : (0 : ℝ) < (12 : ℝ)^(1-(1-C)) := Real.rpow_pos_of_pos (by norm_num) _
    exact div_nonneg (by positivity) (mul_pos hc' hT).le
  · rw [show (1 : ℝ)-(1-C) = C by ring, div_le_iff₀ hden, target_count]
    have h := completion
    push_cast at h ⊢
    linarith

theorem tensor_cutoff_positive : 0 < (12 : ℕ)^12800 := by positivity

theorem tensor_rank_separation : (12 : ℕ)^12800 < 13^12800 := by
  exact Nat.pow_lt_pow_left (by norm_num) (by norm_num)

theorem tensor_floor_fits : (13 : ℕ)^12800 ≤ 145^12800 := by
  gcongr <;> norm_num

end
end FFTChainDFT.Analytic

#print axioms FFTChainDFT.Analytic.strictified_moment
