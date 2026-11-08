import Submission.InventorySupport
import Submission.TensorCertificate

set_option maxRecDepth 16000

namespace FFTChainDFT.Analytic
open TensorProto
noncomputable section

def histCount (l : List (ℕ × ℕ)) (r : ℕ) : ℕ :=
  ((l.filter fun b => b.1 = r).map Prod.snd).sum

theorem target_histogram_link (r : ℕ) :
    histCount targetHist r = Inventory.targetCount r := by
  unfold Inventory.targetCount
  split <;> simp_all [histCount, targetHist, List.filter_cons, eq_comm]

theorem paid_histogram_link (r : ℕ) :
    histCount paidHist r = Inventory.paidCount r := by
  unfold Inventory.paidCount
  split <;> simp_all [histCount, paidHist, List.filter_cons, eq_comm]

/-- The multiset in the analytic certificate retains the original multiplicities. -/
theorem count_ofHist (l : List (ℕ × ℕ)) (r : ℕ) :
    Multiset.count r (ofHist l) = histCount l r := by
  induction l with
  | nil => simp [ofHist, histCount]
  | cons b l ih =>
    have e : ofHist (b :: l) = Multiset.replicate b.2 b.1 + ofHist l := by
      simp [ofHist]
    rw [e, Multiset.count_add, ih]
    by_cases h : b.1 = r <;>
      simp [histCount, h, Multiset.count_replicate, List.filter_cons]

theorem productive_multiset_link (r : ℕ) :
    Multiset.count r (ofHist targetHist) = Inventory.targetCount r := by
  rw [count_ofHist, target_histogram_link]

theorem paid_multiset_link (r : ℕ) :
    Multiset.count r (ofHist paidHist) = Inventory.paidCount r := by
  rw [count_ofHist, paid_histogram_link]

/-- The completion floor is attained, because the raw inventory contains rank one. -/
theorem tensor_floor_attained_at (v : ℕ) :
    13^v ∈ strictT (ofHist targetHist) v (13^v) := by
  have hc : 0 < Multiset.count 1 (ofHist targetHist) := by
    rw [productive_multiset_link]; decide
  have h1 : 1 ∈ ofHist targetHist := Multiset.count_pos.mp hc
  exact mem_padT (pow_mem_tpow h1 v)
    (Nat.pow_le_pow_left (by norm_num : (1 : ℕ) ≤ 13) v)

theorem tensor_floor_attained (v : ℕ) :
    13^v ∈ strictT (ofHist targetHist) v (13^v) :=
  tensor_floor_attained_at v

theorem strictified_rank_bounds :
    (∀ r ∈ strictP (ofHist targetHist) (ofHist paidHist) 12800
      (12^12800) (13^12800), r ≤ 12^12800) ∧
    (∀ r ∈ strictT (ofHist targetHist) 12800 (13^12800), 13^12800 ≤ r) ∧
    (12 : ℕ)^12800 < 13^12800 :=
  strictify_sep (by norm_num) (by norm_num) (by norm_num)

end
end FFTChainDFT.Analytic
