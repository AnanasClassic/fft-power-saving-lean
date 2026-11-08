import Submission.Chain.Engine
import Submission.Chain.Physical.RawCertificate
/-! The new exact kernel program. Only the newly assembled finite witness
and the proved moment inequality enter this theorem; the previous final DFT
bound is not used. The generic engines retain their upstream attribution. -/
namespace FFTChainDFT
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
universe u

theorem engine (cl : Paint) (m : Bool) {ι : Type u} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1-(6727247:ℝ)/2000000000) (k i)) := by
  obtain ⟨α,ρ,σ,i1,i2,i3,i4,i5,i6,e,tr,tz,w,G,he,hind,hP,hLive,hG,hα,htr,hcnt,hhist⟩ := Finite.rawCert_exists
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  exact TensorEng.chain18_engine_of_rawG e tr tz w G he hind hP hLive hG hα htr hcnt hhist
    (by norm_num [Analytic.C]) (by norm_num) m cl k v
end
end FFTChainDFT
#print axioms FFTChainDFT.engine
