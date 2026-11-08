import Submission.Work.FwdOnly.Gen.P104WSchedR
import Mathlib
/-! Residual-slot counting proofs adapted from Kartal LFBaseP104W.
The modified supplier preserves this exit-label table; Supplier.helper_residual
is the semantic bridge, used by Native.HelperHistogram. -/
namespace FFTChainDFT.Native.HelperData
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
lemma sum_range_getD {M : Type*} [AddCommMonoid M] (L : List ℕ) (g : ℕ → M) :
    ∑ i ∈ Finset.range L.length, g (L.getD i 0) = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact add_comm _ _

lemma schedRes_length : GXD.P104W.schedRes.length = 562 := by decide +kernel

/-- the residual ranks of the 562 slots: 385 of 9, 19 of 8, 9 of 7, 2 of 6, 14 of 5, 107 of 4, 4 of 3, 8 of 2, 14 of 1. -/
theorem res_sum (g : ℕ → ℝ) :
    ∑ q : Fin 562, g (GXD.P104W.schedRes.getD q.val 0)
      = 385 * g 9 + 19 * g 8 + 9 * g 7 + 2 * g 6 + 14 * g 5 + 107 * g 4 + 4 * g 3 + 8 * g 2 + 14 * g 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (GXD.P104W.schedRes.getD i 0)) 562, ← schedRes_length,
    sum_range_getD]
  simp only [GXD.P104W.schedRes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- the same count in `ℕ`. -/
theorem res_sumN (g : ℕ → ℕ) :
    ∑ q : Fin 562, g (GXD.P104W.schedRes.getD q.val 0)
      = 385 * g 9 + 19 * g 8 + 9 * g 7 + 2 * g 6 + 14 * g 5 + 107 * g 4 + 4 * g 3 + 8 * g 2 + 14 * g 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (GXD.P104W.schedRes.getD i 0)) 562, ← schedRes_length,
    sum_range_getD]
  simp only [GXD.P104W.schedRes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

lemma schedRes_bounds : ∀ i < 562, 1 ≤ GXD.P104W.schedRes.getD i 0 ∧ GXD.P104W.schedRes.getD i 0 ≤ 9 := by
  decide +kernel

lemma res_bounds (q : Fin 562) :
    1 ≤ GXD.P104W.schedRes.getD q.val 0 ∧ GXD.P104W.schedRes.getD q.val 0 ≤ 9 :=
  schedRes_bounds q.val q.isLt

end FFTChainDFT.Native.HelperData
#print axioms FFTChainDFT.Native.HelperData.res_sumN
#print axioms FFTChainDFT.Native.HelperData.schedRes_bounds
