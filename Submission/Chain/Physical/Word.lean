import Submission.Chain.Physical.RawCompiler
import Submission.Chain.Physical.RoleSets
import Submission.Chain.ScheduleHistogram
import Submission.Work.Mixed.HeadM1
/-! Full live-kernel certificate for the physical paired controller.
The free helper adapters follow Sussman's fresh_frames and Kartal's BQ19
wordCert. The new endpoint is the literal paired 9+9 controller, not BQ19.
All main and helper statements below hold for arbitrary input arrays. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
  {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H=9)
  (hOk : ∀ n d, Ok (ChainG18.winN l hH n d))

def mainTarget (i : Fin 40) := StageSets.targetSet l (Schedule.targetStages i)

def mainCorrection (g : Orth (LC (Fin 17) H l)) (i : Fin 40) (t : T) : Space (LC (Fin 17) H l) :=
  (ChainG18.basisA base l g t).v (Sum.inl l) + (ChainG18.basisA base l g t).corr (mainTarget l i)

def correctionR : PRole (Orth (LC (Fin 17) H l)) T Sl C → Space (LC (Fin 17) H l)
  | .inl (.inl (g,(i,t))) => mainCorrection base l g i t
  | _ => 0

def rawTz (D : Sl → Finset (LC (Fin 17) H l)) : PLive (Orth (LC (Fin 17) H l)) T Sl →
    Σ r : ℕ, Fin r → Space (LC (Fin 17) H l)
  | .inl (g,(i,t)) => ⟨(mainTarget l i).card,(ChainG18.basisA base l g t).fam (mainTarget l i)⟩
  | .inr (_,(_,q)) => ⟨(D q).card,FH.targ (D q)⟩

theorem rawTz_indep (D : Sl → Finset (LC (Fin 17) H l)) (p : PLive (Orth (LC (Fin 17) H l)) T Sl) :
    LinearIndependent F (rawTz base l D p).2 := by
  rcases p with ⟨g,i,t⟩|⟨g,k,q⟩
  · exact OBase.fam_indep (ChainG18.basisA base l g t) (mainTarget l i)
  · exact FH.targ_indep (D q)

include hbase hOk in
 theorem final_main (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (i : Fin 40) (t : T) :
    matAct f (Binary.shift (mainCorrection base l g i t))
      (rawList I base l hbase hH hOk Schedule.code f v (mainR g i t)) =
      matAct f (blockMat ((ChainG18.basisA base l g t).fam (mainTarget l i))) (v (mainR g i t)) := by
  apply P4L.normal_qi f (ChainG18.basisA base l g t) (mainTarget l i) (Sum.inl l)
  funext z
  rw [raw_main_endpoint I base l hbase hH hOk]
  have ht := StageSets.target_phase_at l f (ChainG18.basisA base l g t)
    (Schedule.targetStages i) (Schedule.target_stages_nodup i) z
  have hqi := congrFun (P4L.qi_split f (ChainG18.basisA base l g t) (Sum.inl l)) z
  rw [FFTChainDFT.PhysicalPhase.inverse_phase_cube] at hqi
  change (pivotQ base l f g t z)^3 = pivotQ base l f g t z *
    P4L.prodF f (fun x => sign (dot ((ChainG18.basisA base l g t).v (Sum.inl l)) x)) z at hqi
  change _ = _ * P4L.prodF f (P4L.fr (ChainG18.basisA base l g t)
    (StageSets.targetSet l (Schedule.targetStages i))) z * _
  rw [ht,hqi]
  simp only [stageD,pivotQ]
  ring

include hbase hOk in
 theorem wordCert (D : Sl → Finset (LC (Fin 17) H l))
    (hD : ∀ q, (D q).card=Fintype.card H-(I.ent q).dim) :
    ∃ w : GWord (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C),
      w.Proper (Fintype.card (LC (Fin 17) H l)) ∧
      (∀ φ, w.costR φ = (Schedule.code.map (fun op => opcodePrice I l op φ)).sum) ∧
      MX.GLiveKernelM
        (fun p : PLive (Orth (LC (Fin 17) H l)) T Sl => (Sum.inl p : PRole (Orth (LC (Fin 17) H l)) T Sl C))
        (fun p => blockMat (rawTz base l D p).2) w := by
  have hfc : ∀ k : Fin 36, ∃ Zp : Orth (LC (Fin 17) H l) → Sl → CMat (LC (Fin 17) H l),
      (∀ g q, GReach 1 (Zp g q) (fun _ => 0)) ∧
      (∀ g q, GReach (bankResidual I l hH k g q * Zp g q) (pk (D q)) (fun _ => 0)) := by
    intro k
    obtain ⟨Z,hZ,hend⟩ := P4L.fresh_call (bankResidual I l hH k)
      (fun q => Fintype.card H-(I.ent q).dim) (fun g q => entW_form _ (I.ent q)) D
      (fun q => (hD q).ge) (fun q => by rw [hD q,Nat.sub_self,ChainG18.card_LC145 l hH]; norm_num)
    exact ⟨Z,hZ,fun g q => (hend g q).cast (fun φ => by rw [hD q,Nat.sub_self,bcost_zero])⟩
  choose Zp hZ1 hZ2 using hfc
  obtain ⟨U,hU,Rpre⟩ := P4L.ORoute.steps (freshAll (Γ := Orth (LC (Fin 17) H l)) (T := T) (Sl := Sl) (C := C))
    (fun _ => 1) (freshMat Zp) (fun _ _ => 0) (fun r hr => by
      obtain ⟨g,k,q,rfl⟩ := of_mem_freshAll hr
      exact hZ1 k g q _ (freshR g k q))
  obtain ⟨V,hV,Rpost⟩ := P4L.ORoute.steps (freshAll (Γ := Orth (LC (Fin 17) H l)) (T := T) (Sl := Sl) (C := C))
    (fun r => freshMat (bankResidual I l hH) r * freshMat Zp r) (freshTgt D)
    (fun _ _ => 0) (fun r hr => by
      obtain ⟨g,k,q,rfl⟩ := of_mem_freshAll hr
      exact hZ2 k g q _ (freshR g k q))
  have Rsh := P4L.ORoute.steps_inv (mainAll (Γ := Orth (LC (Fin 17) H l)) (T := T) (Sl := Sl) (C := C))
    (fun _ => 1) (fun _ => 1) (fun r => Binary.shift (correctionR (Sl := Sl) (C := C) base l r))
    (fun _ _ => Matrix.mul_one 1) (fun _ _ => 0) (fun r _ => P4L.gstep_shift r _)
  have Rm := rawList_route I base l hbase hH hOk Schedule.code Schedule.valid_ops
  obtain ⟨w,hw,hc,hwalk⟩ := ((Rpre.trans Rm).trans Rpost).trans Rsh
  refine ⟨w,hw,fun φ => (hc φ).trans (by simp only [Finset.sum_const_zero,zero_add,add_zero]),?_⟩
  intro f v hv p
  rcases p with ⟨g,i,t⟩|⟨g,k,q⟩
  · change gwalk f w v (mainR g i t) =
      matAct f (blockMat ((ChainG18.basisA base l g t).fam (mainTarget l i))) (v (mainR g i t))
    rw [hwalk f v]
    try dsimp only
    rw [if_pos (main_mem_mainAll (Sl := Sl) (C := C) g i t),
      if_neg (main_not_freshAll (Sl := Sl) (C := C) g i t),Matrix.mul_one]
    change matAct f (Binary.shift (mainCorrection base l g i t)) _ = _
    rw [final_main I base l hbase hH hOk]
    rw [if_neg (main_not_freshAll (Sl := Sl) (C := C) g i t)]
  · change gwalk f w v (freshR g k q) = matAct f (blockMat (FH.targ (D q))) (v (freshR g k q))
    rw [hwalk f v]
    try dsimp only
    rw [if_neg (fresh_not_mainAll (T := T) (C := C) g k q),
      if_pos (fresh_mem_freshAll (T := T) (C := C) g k q),
      raw_fresh_endpoint I base l hbase hH hOk]
    try dsimp only
    rw [if_pos (fresh_mem_freshAll (T := T) (C := C) g k q)]
    have eU : U (freshR g k q)=Zp k g q := by
      have h := hU _ (fresh_mem_freshAll (T := T) (C := C) g k q)
      change U (freshR g k q)*1=Zp k g q at h
      simpa only [Matrix.mul_one] using h
    have eV : V (freshR g k q)*(bankResidual I l hH k g q*Zp k g q)=pk (D q) :=
      hV _ (fresh_mem_freshAll (T := T) (C := C) g k q)
    rw [eU]
    simp only [matAct_mul,Matrix.mul_assoc]
    rw [eV,FH.pk_eq_targ]
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.wordCert
