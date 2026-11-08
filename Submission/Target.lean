import Submission.OAI.Computability.FourierTransform.Goal

/-! The requested statement, using the verifier-owned definitions unchanged.
This definition specifies the goal; it is not a proof of that goal. -/
open OAI.PowerSaving Filter Asymptotics
namespace FFTChainDFT

def Target : Prop :=
  ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (3363623 : ℝ) / 1000000000))

end FFTChainDFT
