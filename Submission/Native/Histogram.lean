import Submission.Work.GCert.Data.Count
import Submission.Native.ModifiedData

/-! Counts of the paid blocks in the concrete modified native word. -/
set_option maxRecDepth 100000
namespace FFTChainDFT.Native
open GXD
 theorem rankBound : wsumK (SSC.wGt 8) ranksMod 0 = 0 := by decide +kernel
theorem rank0_ok : wsumK (SSC.wEq 0) ranksMod 0 = 0 := by decide +kernel
theorem rank1_ok : wsumK (SSC.wEq 1) ranksMod 0 = 2216 := by decide +kernel
theorem rank2_ok : wsumK (SSC.wEq 2) ranksMod 0 = 456 := by decide +kernel
theorem rank3_ok : wsumK (SSC.wEq 3) ranksMod 0 = 496 := by decide +kernel
theorem rank4_ok : wsumK (SSC.wEq 4) ranksMod 0 = 98 := by decide +kernel
theorem rank5_ok : wsumK (SSC.wEq 5) ranksMod 0 = 165 := by decide +kernel
theorem rank6_ok : wsumK (SSC.wEq 6) ranksMod 0 = 8 := by decide +kernel
theorem rank7_ok : wsumK (SSC.wEq 7) ranksMod 0 = 9 := by decide +kernel
theorem rank8_ok : wsumK (SSC.wEq 8) ranksMod 0 = 1 := by decide +kernel
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.rankBound
