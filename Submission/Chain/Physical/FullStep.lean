import Submission.Chain.Physical.NativeStages
import Submission.Chain.Physical.Query
import Submission.Chain.Plan
/-! Pointwise all-array endpoint of every full invocation. The bank number
is part of the literal controller and is linked to its actual geometric stage. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
section Evaluation
variable {Z : Type}
theorem eval_callF (z : Z) (a b : Fin 40) (d qi : Z → ℂ) (u : State (Z → ℂ)) :
    State.map (fun w => w z) (callF a b d qi u) =
      callF a b (d z) (qi z) (State.map (fun w => w z) u) := by
  simp only [callF,State.map_set,State.map_get]
end Evaluation
section Geometry
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
  {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (base : T → OBase H) (l : H) (hH : Fintype.card H=9)

def stageOf (j : Fin 36) : Fin 18 := ⟨j.val/2,by omega⟩
def bankResidual (j : Fin 36) := nativeResidual I l hH (stageOf j)

theorem stage_fullID (k : Fin 18) (a b : Fin 40) (h : Schedule.ValidOp (.full k a b)) :
    stageOf (Schedule.fullID k a) = k :=
  Fin.ext (Schedule.full_id_values k a b h).1

theorem fullID_roles (k : Fin 18) (a b : Fin 40) (h : Schedule.ValidOp (.full k a b)) :
    xOf (Schedule.fullID k a)=a ∧ yOf (Schedule.fullID k a)=b := by
  rcases (Schedule.full_id_values k a b h).2 with ⟨hp,rfl,rfl⟩|⟨hp,rfl,rfl⟩
  · simp only [xOf,yOf,hp,ite_true]
    exact ⟨rfl,rfl⟩
  · simp only [xOf,yOf,hp,show (1:ℕ)≠0 by decide,ite_false]
    exact ⟨rfl,rfl⟩

theorem native_viewAt (j : Fin 36) (k : Fin 18) (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) (z : Sky (LC (Fin 17) H l) f) :
    viewAt f g t z (nativeRun I base l hH j k f v) =
      callF (xOf j) (yOf j) (stageD base l f g t z k) ((pivotQ base l f g t z)^3) (viewAt f g t z v) := by
  have h := congrArg (State.map (fun w => w z)) (native_view I base l hH j k f v g t)
  simpa only [viewAt_eq,eval_callF,FFTChainDFT.PhysicalPhase.inverse_phase_cube,stageD,pivotQ] using h

theorem full_viewAt (k : Fin 18) (a b : Fin 40) (h : Schedule.ValidOp (.full k a b))
    (f : ℕ) (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) (z : Sky (LC (Fin 17) H l) f) :
    viewAt f g t z (nativeRun I base l hH (Schedule.fullID k a) k f v) =
      Op.eval (stageD base l f g t z) (pivotQ base l f g t z) (.full k a b) (viewAt f g t z v) := by
  simpa only [native_viewAt,(fullID_roles k a b h).1,(fullID_roles k a b h).2,callF,Op.eval]
end Geometry
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.full_viewAt
