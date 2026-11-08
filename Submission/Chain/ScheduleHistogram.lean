import Submission.Chain.ScheduleCost
import Submission.Inventory
/-! Uniform histogram of the actual source-call schedule. The independent
physical GWord realization is required to turn this invoice into a program bound. -/
namespace FFTChainDFT.Chain.Schedule
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def paidMultiplicity (r : ℕ) : ℕ :=
  (tags.map fun t => if t=0 then Inventory.paidPerNative r else 104*Inventory.indicator r t).sum

theorem paid_from_schedule (r : ℕ) : paidMultiplicity r = Inventory.paidCount r := by
  unfold paidMultiplicity
  rw [tag_sum]
  by_cases hr : r ≤ 64
  · interval_cases r <;> norm_num [Inventory.paidCount,Inventory.paidPerNative,Inventory.indicator,List.range_succ]
  · have hn : Inventory.paidPerNative r = 0 := by
      unfold Inventory.paidPerNative
      split <;> omega
    have hp : Inventory.paidCount r = 0 := by
      unfold Inventory.paidCount
      split <;> omega
    have hi (s : ℕ) (hs : s ≤ 64) : Inventory.indicator r s = 0 := by
      simp [Inventory.indicator,show r ≠ s by omega]
    norm_num [hn,hp,hi,List.range_succ]

/-- All stage sets in the certified endpoint are ordinary sets, with no
repeated stage transform silently removed by a multiset-to-set conversion. -/
theorem target_stages_nodup : ∀ r : Fin 40, (targetStages r).Nodup := by decide +kernel

theorem main_rank_list : List.ofFn (fun i : Fin 40 => 1+8*(targetStages i).length) =
  [145, 73, 65, 57, 49, 41, 33, 25, 17, 9, 9, 17, 25, 33, 41, 49, 57, 65, 73, 1, 145, 73, 65, 57, 49, 41, 33, 25, 17, 9, 9, 17, 25, 33, 41, 49, 57, 65, 73, 1] := by decide +kernel

def mainMultiplicity (r : ℕ) : ℕ :=
  (List.ofFn (fun i : Fin 40 => 1+8*(targetStages i).length)).count r

def productiveMultiplicity (r : ℕ) : ℕ :=
  36*Inventory.helperPerNative r + 104*mainMultiplicity r

theorem productive_from_endpoints (r : ℕ) : productiveMultiplicity r = Inventory.targetCount r := by
  unfold productiveMultiplicity mainMultiplicity
  rw [main_rank_list]
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 17 ∨ r = 25 ∨ r = 33 ∨ r = 41 ∨ r = 49 ∨ r = 57 ∨ r = 65 ∨ r = 73 ∨ r = 145 ∨ (r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 17 ∧ r ≠ 25 ∧ r ≠ 33 ∧ r ≠ 41 ∧ r ≠ 49 ∧ r ≠ 57 ∧ r ≠ 65 ∧ r ≠ 73 ∧ r ≠ 145) by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h17, h25, h33, h41, h49, h57, h65, h73, h145⟩
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · subst r; norm_num [Inventory.helperPerNative,Inventory.targetCount]
  · simp_all [Inventory.helperPerNative,Inventory.targetCount,List.count_eq_zero]
end FFTChainDFT.Chain.Schedule
#print axioms FFTChainDFT.Chain.Schedule.paid_from_schedule
#print axioms FFTChainDFT.Chain.Schedule.productive_from_endpoints
