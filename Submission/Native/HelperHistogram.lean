import Submission.Native.Provider
import Submission.Native.HelperData
import Submission.Inventory
namespace FFTChainDFT.Native
open OAI.PowerSaving
noncomputable section
/-- Actual exit residuals of the modified supplier, including every one of
its 562 arbitrary-input productive helpers. -/
theorem helper_histogram (r : ℕ) :
    (∑ q : Fin 562, if Fintype.card (Fin 9) - (provider.ent q).dim = r then 1 else 0) =
      Inventory.helperPerNative r := by
  change (∑ q : Fin 562, if Fintype.card (Fin 9) - (ginvW.ent q).dim = r then 1 else 0) = _
  simp_rw [helper_residual]
  rw [HelperData.res_sumN (fun x => if x=r then 1 else 0)]
  by_cases hr : r≤9
  · interval_cases r <;> norm_num [Inventory.helperPerNative]
  · have h1 : r≠1 := by omega
    have h2 : r≠2 := by omega
    have h3 : r≠3 := by omega
    have h4 : r≠4 := by omega
    have h5 : r≠5 := by omega
    have h6 : r≠6 := by omega
    have h7 : r≠7 := by omega
    have h8 : r≠8 := by omega
    have h9 : r≠9 := by omega
    simp [Inventory.helperPerNative,eq_comm,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem helper_rank_bounds (q : Fin 562) :
    1 ≤ Fintype.card (Fin 9) - (provider.ent q).dim ∧
      Fintype.card (Fin 9) - (provider.ent q).dim ≤ 9 := by
  change 1 ≤ Fintype.card (Fin 9) - (ginvW.ent q).dim ∧
    Fintype.card (Fin 9) - (ginvW.ent q).dim ≤ 9
  simp only [helper_residual]
  exact HelperData.res_bounds q
end
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.helper_histogram
#print axioms FFTChainDFT.Native.helper_rank_bounds
