import Submission.Chain.Fourier.Main
open OAI.PowerSaving Filter Asymptotics
/-- The requested exact-DFT saving in the original computational model.
This theorem is accepted only after the physical witness and full reduction
imported above have passed the kernel; no weaker final result is used. -/
theorem Race.bound :
    ∃ order solve W, DFTProgram order solve W ∧
      (fun n : ℕ => (W n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)*(Real.log (n : ℝ))^(1-(3363623:ℝ)/1000000000)) := by
  obtain ⟨order,solve,W,hprogram,htime⟩ := transform_mainChain18
  refine ⟨order,solve,W,hprogram,?_⟩
  have hfun : decimalTimeChain18 =
      (fun n : ℕ => (n : ℝ)*(Real.log (n : ℝ))^(1-(3363623:ℝ)/1000000000)) := rfl
  rw [←hfun]
  exact htime.2.1
#print axioms Race.bound
