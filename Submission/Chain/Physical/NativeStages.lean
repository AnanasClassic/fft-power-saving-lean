import Submission.Chain.Geometry.Lemmas
import Submission.Chain.Physical.FullView
import Submission.Chain.Physical.Phase
/-! Eighteen geometric stages, independently embedded in any of the36
native-call helper banks. The proof follows Kartal BQ19.Stages, using only
forward calls and the new145-dimensional geometry. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
  {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H=9)
  (hOk : ∀ n d, Ok (ChainG18.winN l hH n d))

include hbase in
 theorem stage_frames (s : Fin 18) (g : Orth (LC (Fin 17) H l)) (t : T) :
    let W := ChainG18.winN l hH s.val (ChainG18.gaugeE base l s.val t g)
    (W.Xm.Φ (tt (I.tv t)) = frame (ChainG18.basisA base l g t) (ChainG18.setX l s.val)) ∧
    (W.Xm.Φ 1 = frame (ChainG18.basisA base l g t) (ChainG18.setX l (s.val+1))) ∧
    (W.Xm.Φ 0 = frame (ChainG18.basisA base l g t) (ChainG18.setY l s.val)) ∧
    (W.Xm.Φ (1+tt (I.tv t)) = frame (ChainG18.basisA base l g t) (ChainG18.setY l (s.val+1))) := by
  fin_cases s
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage0_Xin base l t g
    · exact ChainG18.stage0_Xout base l t g
    · exact ChainG18.stage0_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage0_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage1_Xin base l t g
    · exact ChainG18.stage1_Xout base l t g
    · exact ChainG18.stage1_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage1_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage2_Xin base l t g
    · exact ChainG18.stage2_Xout base l t g
    · exact ChainG18.stage2_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage2_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage3_Xin base l t g
    · exact ChainG18.stage3_Xout base l t g
    · exact ChainG18.stage3_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage3_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage4_Xin base l t g
    · exact ChainG18.stage4_Xout base l t g
    · exact ChainG18.stage4_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage4_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage5_Xin base l t g
    · exact ChainG18.stage5_Xout base l t g
    · exact ChainG18.stage5_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage5_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage6_Xin base l t g
    · exact ChainG18.stage6_Xout base l t g
    · exact ChainG18.stage6_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage6_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage7_Xin base l t g
    · exact ChainG18.stage7_Xout base l t g
    · exact ChainG18.stage7_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage7_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage8_Xin base l t g
    · exact ChainG18.stage8_Xout base l t g
    · exact ChainG18.stage8_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage8_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage9_Xin base l t g
    · exact ChainG18.stage9_Xout base l t g
    · exact ChainG18.stage9_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage9_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage10_Xin base l t g
    · exact ChainG18.stage10_Xout base l t g
    · exact ChainG18.stage10_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage10_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage11_Xin base l t g
    · exact ChainG18.stage11_Xout base l t g
    · exact ChainG18.stage11_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage11_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage12_Xin base l t g
    · exact ChainG18.stage12_Xout base l t g
    · exact ChainG18.stage12_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage12_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage13_Xin base l t g
    · exact ChainG18.stage13_Xout base l t g
    · exact ChainG18.stage13_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage13_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage14_Xin base l t g
    · exact ChainG18.stage14_Xout base l t g
    · exact ChainG18.stage14_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage14_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage15_Xin base l t g
    · exact ChainG18.stage15_Xout base l t g
    · exact ChainG18.stage15_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage15_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage16_Xin base l t g
    · exact ChainG18.stage16_Xout base l t g
    · exact ChainG18.stage16_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage16_Yout base l t g
  · refine ⟨?_,?_,?_,?_⟩
    · rw [hbase t]; exact ChainG18.stage17_Xin base l t g
    · exact ChainG18.stage17_Xout base l t g
    · exact ChainG18.stage17_Yin base l t g
    · rw [hbase t]; exact ChainG18.stage17_Yout base l t g

def nativeResidual (s : Fin 18) (g : Orth (LC (Fin 17) H l)) (slot : Sl) : CMat (LC (Fin 17) H l) :=
  entW (ChainG18.winN l hH s.val g).X (I.ent slot)

def nativeRun (j : Fin 36) (s : Fin 18) (f : ℕ)
    (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f) :
    Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f :=
  multiAct f (stT j (ChainG18.basisA base l)
    (ChainG18.setY l s.val ∪ {Sum.inl l} ∪ ChainG18.incr l s.val)
    (ChainG18.setY l s.val ∪ ChainG18.incr l s.val) (nativeResidual I l hH s))
    (point f (gFk j) (multiAct f (stS' j (ChainG18.basisA base l)
      (ChainG18.setY l s.val ∪ {Sum.inl l}) (ChainG18.setY l s.val)) y))

include hbase hOk in
 theorem native_route (j : Fin 36) (s : Fin 18) :
    P4L.ORoute (nativeRun I base l hH j s)
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*I.cost φ) := by
  have eX := (ChainG18.setX_succ l s.val s.isLt).1
  have eY := (ChainG18.setY_succ l s.val s.isLt).1
  have eP := ChainG18.setX_eq l s.val (by omega)
  refine call_fwd I j (ChainG18.gaugeE base l s.val) (ChainG18.winN l hH s.val) (hOk s.val)
    (ChainG18.basisA base l) (ChainG18.setY l s.val ∪ {Sum.inl l})
    (ChainG18.setY l s.val ∪ {Sum.inl l} ∪ ChainG18.incr l s.val)
    (ChainG18.setY l s.val) (ChainG18.setY l s.val ∪ ChainG18.incr l s.val) ?_ ?_ ?_ ?_
  · intro g t
    rw [←eP]
    exact (stage_frames I base l hbase hH s g t).1
  · intro g t
    rw [←eP,←eX]
    exact (stage_frames I base l hbase hH s g t).2.1
  · intro g t
    exact (stage_frames I base l hbase hH s g t).2.2.1
  · intro g t
    rw [←eY]
    exact (stage_frames I base l hbase hH s g t).2.2.2

 theorem native_view (j : Fin 36) (s : Fin 18) (f : ℕ)
    (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) :
    view f g t (nativeRun I base l hH j s f y) =
      callF (xOf j) (yOf j) (P4L.prodF f (P4L.fr (ChainG18.basisA base l g t) (ChainG18.incr l s.val)))
        (P4L.prodF f (fun x => (P4L.fr (ChainG18.basisA base l g t) {Sum.inl l} x)⁻¹)) (view f g t y) := by
  have dX := (ChainG18.setX_succ l s.val s.isLt).2
  have dY := (ChainG18.setY_succ l s.val s.isLt).2
  have dP := (ChainG18.setX_pivot l s.val (by omega)).2
  rw [ChainG18.setX_eq l s.val (by omega)] at dX
  exact view_call_fwd j (ChainG18.basisA base l) (ChainG18.setY l s.val) (ChainG18.incr l s.val)
    (Sum.inl l) dX dY dP (nativeResidual I l hH s) f y g t

 theorem native_fresh (j j' : Fin 36) (s : Fin 18) (f : ℕ)
    (y : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (slot : Sl) :
    nativeRun I base l hH j s f y (freshR g j' slot) =
      if j'=j then matAct f (nativeResidual I l hH s g slot) (y (freshR g j' slot)) else y (freshR g j' slot) := by
  change matAct f (if j'=j then nativeResidual I l hH s g slot * 1 else (1 : CMat (LC (Fin 17) H l)))
    (matAct f (1 : CMat (LC (Fin 17) H l)) (y (freshR g j' slot))) = _
  by_cases h : j'=j <;> simp only [h,ite_true,ite_false,Matrix.mul_one,matAct_one]
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.native_route
#print axioms OAI.PowerSaving.ChainNet.native_view
#print axioms OAI.PowerSaving.ChainNet.native_fresh
