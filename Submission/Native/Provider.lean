import Submission.Native.Supplier
import Submission.Work.XHostT.TProvW
import Submission.Work.P4L.Geom401
namespace FFTChainDFT.Native
open OAI.PowerSaving OAI.PowerSaving.CB OAI.PowerSaving.GF OAI.PowerSaving.GX
noncomputable section
/-- The modified supplier in Sussman's windowed stage interface. -/
def provider : XHostTW.GInvW (Fin 9) (Fin 104) (Fin 562) (Fin 29) okW :=
  ⟨ginvW.tv, ginvW.hunit, ginvW.hgap, ginvW.cost, ginvW.ent, ginvW.fwd, ginvW.bwd⟩
theorem provider_cost (φ : ℕ → ℝ) : provider.cost φ = invPrice φ := ginv_cost φ

/-- The free wrapper works for arbitrary block types, including Fin 17. -/
theorem okC_generic {B : Type} [Fintype B] [DecidableEq B]
    (hB : 1 ≤ Fintype.card B) (l : Fin 9) (hH2 : 2 ≤ Fintype.card (Fin 9))
    (d : RF.Orth (BC.LC B (Fin 9) l)) (q : Finset (B × BC.Hp (Fin 9) l)) :
    okW (GX.gwinC hB hH2 d q) :=
  FwdOnly.wrapOK_gwinC wc.tv hunit hB hH2 d q

/-- Native port vectors admit the pivot bases required by the bridged geometry.
This is the same general base completion used in the prior submissions. -/
theorem base_exists (l : Fin 9) :
    ∃ base : Fin 104 → OBase (Fin 9), ∀ t, provider.tv t = (base t).v l := by
  have hb : ∀ t, ∃ A : OBase (Fin 9), provider.tv t = A.v l :=
    fun t => GX.base_ex (provider.tv t) (provider.hunit t) (provider.hgap t) l
  choose base hbase using hb
  exact ⟨base,hbase⟩
end
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.provider
#print axioms FFTChainDFT.Native.okC_generic
#print axioms FFTChainDFT.Native.base_exists
