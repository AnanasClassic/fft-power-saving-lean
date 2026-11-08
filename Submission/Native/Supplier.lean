import Submission.Work.FwdOnly.KFwd
import Submission.Work.FwdOnly.Gen.P104WTab0
import Submission.Work.FwdOnly.Gen.P104WTab1
import Submission.Work.FwdOnly.Gen.P104WTab2
import Submission.Work.FwdOnly.Gen.P104WTab3
import Submission.Work.FwdOnly.Gen.P104WWT
import Submission.Work.FwdOnly.Gen.P104WEnds
import Submission.Work.FwdOnly.Gen.P104WRows
import Submission.Work.FwdOnly.Gen.P104WScF0
import Submission.Work.FwdOnly.Gen.P104WScF1
import Submission.Work.FwdOnly.Gen.P104WScF2
import Submission.Work.FwdOnly.Gen.P104WScF5
import Submission.Work.FwdOnly.Gen.P104WScF6
import Submission.Work.FwdOnly.Gen.P104WRes
import Submission.Work.FwdOnly.Gen.P104WSchedR
import Submission.Native.Scalar3
import Submission.Native.Scalar4
import Submission.Native.Labels
import Submission.Native.Histogram
import Submission.Work.GCert.Data.Price
import Submission.Work.KLowW.Win
import Submission.Work.PWGen.Roles
import Submission.Work.Bridge401.GGeom

/-!
The actual modified forward-only native supplier, using the sound KLW checker.
The proof follows Kartal's P104WWC/P104WGlue integration and Sussman's
forward warp certificate. The edits are credited in ModifiedData. Every
changed computational certificate below is accepted by the Lean kernel.
-/
set_option maxRecDepth 100000
set_option linter.unusedVariables false
namespace FFTChainDFT.Native
open GXD OAI.PowerSaving OAI.PowerSaving.CB OAI.PowerSaving.GF OAI.PowerSaving.GX
noncomputable section

theorem table_ok : GLab.tabK 9 GXD.P104W.tab = true :=
  GLab.tabK_node _ _ _ (GLab.tabK_node _ _ _ GXD.P104W.tab0_ok GXD.P104W.tab2_ok)
    (GLab.tabK_node _ _ _ GXD.P104W.tab1_ok GXD.P104W.tab3_ok)

def wc : KLW.WCert :=
  { v := 104, R := 562, nc := 29, p := GXD.P104W.par, wt := GXD.P104W.wt,
    evs := evsMod, evsB := evsMod, S0 := GXD.P104W.st0, SF := GXD.P104W.stF,
    rs := ranksMod, ports := GXD.P104W.ports, gl := GXD.P104W.gl,
    el := GXD.P104W.exits, q := GXD.P104W.spw, R0 := GXD.P104W.rf0,
    RF := GXD.P104W.rfF, RB := GXD.P104W.rfF }

theorem scalar_all : KLW.ScalOK GXD.P104W.spw false evsMod GXD.P104W.rf0 GXD.P104W.rfF :=
  KLW.ScalOK.append (KLW.ScalOK.of_check GXD.P104W.scF0_ok)
    (KLW.ScalOK.append (KLW.ScalOK.of_check GXD.P104W.scF1_ok)
    (KLW.ScalOK.append (KLW.ScalOK.of_check GXD.P104W.scF2_ok)
    (KLW.ScalOK.append (KLW.ScalOK.of_check scalar3_ok)
    (KLW.ScalOK.append (KLW.ScalOK.of_check scalar4_ok)
    (KLW.ScalOK.append (KLW.ScalOK.of_check GXD.P104W.scF5_ok)
    (KLW.ScalOK.of_check GXD.P104W.scF6_ok))))))

theorem valid : FwdOnly.KF.WValidFS wc where
  hn := rfl
  nr := rfl
  tab := table_ok
  run := KLW.RunW.of_seg table_ok GXD.P104W.wt_ok labels_ok
  ends := GXD.P104W.ends_ok
  par := KLW.ParOK.of_scalW GXD.P104W.scF0_ok
  scF := scalar_all
  id0 := GXD.P104W.id0_ok
  wfF := GXD.P104W.wfF_ok
  shF := GXD.P104W.shF_ok
  frF := GXD.P104W.frF_ok

def okW : ∀ {α : Type} [Fintype α] [DecidableEq α], GWin (Fin 9) α → Prop :=
  fun W => FwdOnly.WrapOK wc.tv W

theorem roles_ok : KLW.WRoles wc (PWG.embB 104 562 29)
    (PWG.unB 104 562 29 (by decide)) :=
  FwdOnly.KF.rolesF wc valid (by decide) (by decide)

def ginvXW : KLW.GInvXW (Fin 9) (Fin 104) (Fin 562) (Fin 29) okW :=
  valid.invW roles_ok okW (fun W _ => FwdOnly.KF.warpFree 9 W.X) (fun W h => h)

def ginvW : KLW.GInvEW (Fin 9) (Fin 104) (Fin 562) (Fin 29) okW := ginvXW.toEW'

theorem hunit : ∀ t, Binary.dot (wc.tv t) (wc.tv t) = 1 := ginvXW.hunit

theorem okC : ∀ (l : Fin 9) (hH2 : 2 ≤ Fintype.card (Fin 9))
    (d : RF.Orth (BC.LC (Fin 8) (Fin 9) l))
    (q : Finset (Fin 8 × BC.Hp (Fin 9) l)),
    okW (GX.gwinC GX.hB401 hH2 d q) :=
  fun _ hH2 d q => FwdOnly.wrapOK_gwinC wc.tv hunit GX.hB401 hH2 d q

def invPrice (φ : ℕ → ℝ) : ℝ :=
  2216*φ 1 + 456*φ 2 + 496*φ 3 + 98*φ 4 + 165*φ 5 + 8*φ 6 + 9*φ 7 + φ 8

theorem rank_cost (φ : ℕ → ℝ) : rcost φ ranksMod = invPrice φ := by
  rw [GXD.rcost_wsumK φ ranksMod 8 rankBound]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    rank0_ok, rank1_ok, rank2_ok, rank3_ok, rank4_ok, rank5_ok, rank6_ok,
    rank7_ok, rank8_ok]
  norm_num [bcost, invPrice]

theorem ginv_cost (φ : ℕ → ℝ) : ginvW.cost φ = invPrice φ := by
  show rcost φ ranksMod = invPrice φ
  exact rank_cost φ

theorem helper_residual (q : Fin 562) :
    Fintype.card (Fin 9) - (ginvW.ent q).dim = GXD.P104W.schedRes.getD q.val 0 := by
  show Fintype.card (Fin 9) - (ginvXW.entS q).dim = _
  rw [ginvXW.entS_hd q, GXD.P104W.schedRes_eq]
  exact (FwdOnly.KF.resF valid roles_ok q).trans (GXD.P104W.res_ok q)

end
end FFTChainDFT.Native
#print axioms FFTChainDFT.Native.valid
#print axioms FFTChainDFT.Native.ginvW
#print axioms FFTChainDFT.Native.ginv_cost
#print axioms FFTChainDFT.Native.helper_residual
