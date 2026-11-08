import Submission.Work.KLowW.LabK
import Submission.Native.ModifiedData

/-! Kernel replay of every frame transition of the modified 22,836-event word. -/
set_option maxRecDepth 100000
namespace FFTChainDFT.Native
open GXD.P104W
 theorem labels_ok : KLW.segW par wt evsMod st0 stF ranksMod = true := by
  decide +kernel
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.labels_ok
