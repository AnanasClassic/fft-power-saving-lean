import Submission.Work.P4L.Basis
namespace FFTChainDFT.PhysicalPhase
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.P4L
noncomputable section
variable {α : Type} [Fintype α] [DecidableEq α]

theorem fr_four (A : OBase α) (s : Finset α) (x : Space α) : (fr A s x)^4=1 := by
  change (lum (A.proj s x))^4=1
  calc
    _ = (lum (A.proj s x)*lum (A.proj s x))^2 := by ring
    _ = 1 := by rw [lum_sq,pow_two,sign_sq]

theorem phase_four (f : ℕ) (A : OBase α) (s : Finset α) (z : Sky α f) : (prodF f (fr A s) z)^4=1 := by
  simp only [prodF,←Finset.prod_pow,fr_four,Finset.prod_const_one]

theorem inverse_phase_cube (f : ℕ) (A : OBase α) (s : Finset α) (z : Sky α f) :
    prodF f (fun x => (fr A s x)⁻¹) z = (prodF f (fr A s) z)^3 := by
  have hmul := congrFun (prodF_inv_mul f A s) z
  have h4 := phase_four f A s z
  have hq : prodF f (fr A s) z ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : 4≠0)] at h4
    exact zero_ne_one h4
  apply mul_right_cancel₀ hq
  simpa only [Pi.mul_apply,Pi.one_apply,←pow_succ] using hmul.trans h4.symm
end
end FFTChainDFT.PhysicalPhase
#print axioms FFTChainDFT.PhysicalPhase.inverse_phase_cube
