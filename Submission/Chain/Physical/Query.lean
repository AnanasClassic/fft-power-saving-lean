import Submission.Chain.Physical.Windows
/-! One paid rank-one query with arbitrary old scratch contents. The source
copy overwrites scratch before the operator is applied. Adapted from Kartal's
thin query machinery; the scalar endpoint is evaluated on independent arrays. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
section ThinMain
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ]
  [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
theorem thin_main (x y i : Fin 40) (j : Fin 6) (U : Γ → T → CMat α)
    (f : ℕ) (v : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    thinOp x y j U f v (mainR g i t) =
      if i=y then v (mainR g i t) + matAct f (U g t) (v (mainR g x t)) else v (mainR g i t) := by
  have hz : zR (Sl := Sl) (C := C) g j t ∈ zSet j := by
    rw [mem_zSet]; exact ⟨g,t,rfl⟩
  by_cases hi : i=y
  · subst i
    unfold thinOp
    rw [addM_y]
    simp only [ite_true,if_neg (main_not_zSet j g y t),if_pos hz,zMat_z,
      Matrix.mul_one,copyM_main,copyM_z]
  · unfold thinOp
    rw [addM_main y j f _ g i t hi]
    simp only [if_neg hi,if_neg (main_not_zSet j g i t),copyM_main]
end ThinMain
section Geometry
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (base : T → OBase H) (l : H) (hH : Fintype.card H=9)

def query_step (a b : Fin 40) (hab : a≠b) :
    SimpleStep (Sl := Sl) (C := C) (stageD base l) (pivotQ base l) (.query a b)
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*(Fintype.card T : ℝ)*bcost φ 1) := by
  let U := fun g t => unframe (ChainG18.basisA base l g t) {Sum.inl l}
  have hdim : 1<Fintype.card (LC (Fin 17) H l) := by
    rw [ChainG18.card_LC145 l hH]; norm_num
  refine ⟨thinOp b a 0 U,
    (thin_route b a hab.symm 0 U (fun φ => bcost φ 1)
      (fun g t => greach_unframe_single _ _ hdim)).cast (fun _ _ => rfl) ?_, ?_, ?_⟩
  · intro φ
    simp only [Finset.sum_const,Finset.card_univ,card_zSet,nsmul_eq_mul,Nat.cast_mul]
  · intro f v g t z
    apply State.ext_get
    intro i
    rw [viewAt_get,thin_main]
    by_cases hi : i=a
    · subst i
      simp only [ite_true,Op.eval,State.get_set_same,viewAt_get]
      rw [P4L.walsh_add,P4L.walsh_unframe]
      simp only [Pi.add_apply,Pi.mul_apply]
      rw [FFTChainDFT.PhysicalPhase.inverse_phase_cube]
      rfl
    · simp only [if_neg hi,Op.eval,State.get_set_ne _ _ _ _ hi,viewAt_get]
  · exact thin_fresh b a 0 U
end Geometry
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.query_step
