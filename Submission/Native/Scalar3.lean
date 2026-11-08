import Submission.Work.KLowW.ScalK
import Submission.Native.ModifiedData

/-! Kernel replay of modified native segment 3. See ModifiedData for attribution. -/
set_option maxRecDepth 100000
namespace FFTChainDFT.Native
open GXD.P104W
 theorem scalar3_ok : KLW.scalW spw false ev3mod GXD.P104W.rfM3 rfMidMod = true := by
  decide +kernel
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.scalar3_ok
