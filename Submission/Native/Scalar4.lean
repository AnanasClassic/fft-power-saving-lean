import Submission.Work.KLowW.ScalK
import Submission.Native.ModifiedData

/-! Kernel replay of modified native segment 4. See ModifiedData for attribution. -/
set_option maxRecDepth 100000
namespace FFTChainDFT.Native
open GXD.P104W
 theorem scalar4_ok : KLW.scalW spw false ev4mod rfMidMod GXD.P104W.rfM5 = true := by
  decide +kernel
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.scalar4_ok
