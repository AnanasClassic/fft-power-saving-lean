import Submission.Chain.Physical.FullStep
import Submission.Chain.Compiler
import Mathlib.Data.List.FinRange
/-! Physical interpretation of the literal paired controller. Every instruction
supplies a proper word, an all-array main transformation and its complete effect
on productive helpers. Each of the 36 independent banks is invoked once. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000

def bankOf : Op → Option (Fin 36)
  | .full k a _ => some (Schedule.fullID k a)
  | _ => none

def nativeBanks (ops : List Op) : List (Fin 36) := ops.filterMap bankOf

theorem native_banks_code : nativeBanks Schedule.code = List.finRange 36 := by decide +kernel

theorem native_bank_once (j : Fin 36) : (nativeBanks Schedule.code).count j = 1 := by
  rw [native_banks_code]
  exact List.count_finRange j

section Abstract
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ]
  [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (d : ∀ f : ℕ, Γ → T → Sky α f → Fin 18 → ℂ)
  (q : ∀ f : ℕ, Γ → T → Sky α f → ℂ) (W : Fin 36 → Γ → Sl → CMat α)

def helperOp (op : Op) (g : Γ) (k : Fin 36) (s : Sl) : CMat α :=
  if some k = bankOf op then W k g s else 1

structure RawStep (op : Op) (price : (ℕ → ℝ) → ℝ) where
  run : ∀ f : ℕ, Data α (PRole Γ T Sl C) f → Data α (PRole Γ T Sl C) f
  route : P4L.ORoute run price
  main : ∀ f y g t z, viewAt f g t z (run f y) = Op.eval (d f g t z) (q f g t z) op (viewAt f g t z y)
  fresh : ∀ f y g k s, run f y (freshR g k s) = matAct f (helperOp W op g k s) (y (freshR g k s))

def liftSimple {op : Op} {price : (ℕ → ℝ) → ℝ}
    (S : SimpleStep (Sl := Sl) (C := C) d q op price) (h : bankOf op=none) : RawStep (Sl := Sl) (C := C) d q W op price where
  run := S.run
  route := S.route
  main := S.main
  fresh := by
    intro f y g k s
    simpa only [helperOp,h,reduceCtorEq,ite_false,matAct_one] using S.fresh f y g k s
end Abstract

section Geometry
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
  {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H=9)
  (hOk : ∀ n d, Ok (ChainG18.winN l hH n d))

def opcodePrice : Op → (ℕ → ℝ) → ℝ
  | .full _ _ _ => fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*I.cost φ
  | .query _ _ => fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*(Fintype.card T : ℝ)*bcost φ 1
  | .idle _ ks => fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*(Fintype.card T : ℝ)*bcost φ (8*ks.length)
  | _ => fun _ => 0

include hbase hOk in
 def full_step (k : Fin 18) (a b : Fin 40) (h : Schedule.ValidOp (.full k a b)) :
    RawStep (Sl := Sl) (C := C) (stageD base l) (pivotQ base l) (bankResidual I l hH)
      (.full k a b) (opcodePrice I l (.full k a b)) where
  run := nativeRun I base l hH (Schedule.fullID k a) k
  route := native_route I base l hbase hH hOk (Schedule.fullID k a) k
  main := full_viewAt I base l hH k a b h
  fresh := by
    intro f y g j s
    rw [native_fresh]
    simp only [helperOp,bankOf,Option.some.injEq]
    by_cases hj : j=Schedule.fullID k a
    · subst j
      simp only [ite_true,bankResidual,stage_fullID k a b h]
    · simp only [if_neg hj,matAct_one]

include hbase hOk in
 def rawInstruction (op : Op) (h : Schedule.ValidOp op) :
    RawStep (Sl := Sl) (C := C) (stageD base l) (pivotQ base l) (bankResidual I l hH) op (opcodePrice I l op) := by
  cases op with
  | add a b c => exact liftSimple _ _ _ (add_step _ _ a b c) rfl
  | scale a c => exact liftSimple _ _ _ (scale_step _ _ a c) rfl
  | swap a b => exact liftSimple _ _ _ (swap_step _ _ a b h) rfl
  | shift a => exact liftSimple _ _ _ (shift_step base l a) rfl
  | had a b => exact liftSimple _ _ _ (had_step _ _ a b h) rfl
  | hadInv a b => exact liftSimple _ _ _ (hadInv_step _ _ a b h) rfl
  | query a b => exact liftSimple _ _ _ (query_step base l hH a b h) rfl
  | full k a b => exact full_step I base l hbase hH hOk k a b h
  | idle a ks => exact liftSimple _ _ _ (idle_step base l hH a ks h.1 h.2.1 h.2.2) rfl

include hbase hOk in
 def rawRun (op : Op) (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f) :=
  if h : Schedule.ValidOp op then (rawInstruction I base l hbase hH hOk op h).run f v else v

include hbase hOk in
 theorem rawRun_route (op : Op) (h : Schedule.ValidOp op) :
    P4L.ORoute (rawRun I base l hbase hH hOk op) (opcodePrice I l op) := by
  exact (rawInstruction I base l hbase hH hOk op h).route.cast
    (fun f y => by simp only [rawRun,dif_pos h]) (fun _ => rfl)

include hbase hOk in
 theorem rawRun_main (op : Op) (h : Schedule.ValidOp op) (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) (z : Sky (LC (Fin 17) H l) f) :
    viewAt f g t z (rawRun I base l hbase hH hOk op f v) =
      Op.eval (stageD base l f g t z) (pivotQ base l f g t z) op (viewAt f g t z v) := by
  simpa only [rawRun,dif_pos h] using (rawInstruction I base l hbase hH hOk op h).main f v g t z

include hbase hOk in
 theorem rawRun_fresh (op : Op) (h : Schedule.ValidOp op) (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (k : Fin 36) (s : Sl) :
    rawRun I base l hbase hH hOk op f v (freshR g k s) =
      matAct f (helperOp (bankResidual I l hH) op g k s) (v (freshR g k s)) := by
  simpa only [rawRun,dif_pos h] using (rawInstruction I base l hbase hH hOk op h).fresh f v g k s

include hbase hOk in
 def rawList (ops : List Op) (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f) :=
  interpret (fun op => rawRun I base l hbase hH hOk op f) ops v

include hbase hOk in
 theorem rawList_route (ops : List Op) (h : ∀ op∈ops, Schedule.ValidOp op) :
    P4L.ORoute (rawList I base l hbase hH hOk ops) (fun φ => (ops.map (fun op => opcodePrice I l op φ)).sum) := by
  induction ops with
  | nil => exact P4L.ORoute.refl
  | cons a ops ih =>
    exact ((rawRun_route I base l hbase hH hOk a (h a List.mem_cons_self)).trans
      (ih (fun op hop => h op (List.mem_cons_of_mem a hop)))).cast (fun _ _ => rfl) (fun _ => rfl)

include hbase hOk in
 theorem rawList_fresh (ops : List Op) (h : ∀ op∈ops, Schedule.ValidOp op) (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (k : Fin 36) (s : Sl) :
    rawList I base l hbase hH hOk ops f v (freshR g k s) =
      matAct f ((bankResidual I l hH k g s)^((nativeBanks ops).count k)) (v (freshR g k s)) := by
  induction ops generalizing v with
  | nil => simp only [rawList,interpret,List.foldl_nil,nativeBanks,List.filterMap_nil,List.count_nil,pow_zero,matAct_one]
  | cons a ops ih =>
    change rawList I base l hbase hH hOk ops f (rawRun I base l hbase hH hOk a f v) (freshR g k s) = _
    rw [ih (fun op hop => h op (List.mem_cons_of_mem a hop)),rawRun_fresh I base l hbase hH hOk a (h a List.mem_cons_self)]
    by_cases ha : some k = bankOf a
    · have hc : (nativeBanks (a::ops)).count k = (nativeBanks ops).count k+1 := by
        simp only [nativeBanks,List.filterMap_cons,←ha,List.count_cons_self]
      rw [helperOp,if_pos ha,matAct_mul,←pow_succ,hc]
    · have hc : (nativeBanks (a::ops)).count k = (nativeBanks ops).count k := by
        cases hb : bankOf a with
        | none => simp only [nativeBanks,List.filterMap_cons,hb]
        | some j =>
          have hj : j≠k := by rintro rfl; exact ha hb.symm
          simp only [nativeBanks,List.filterMap_cons,hb,List.count_cons_of_ne hj]
      rw [helperOp,if_neg ha,matAct_one,hc]

include hbase hOk in
 theorem raw_main_endpoint (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (t : T) (z : Sky (LC (Fin 17) H l) f) (i : Fin 40) :
    P4L.walsh f (rawList I base l hbase hH hOk Schedule.code f v (mainR g i t)) z =
      (pivotQ base l f g t z)^3 * ((Schedule.targetStages i).map (stageD base l f g t z)).prod *
        P4L.walsh f (v (mainR g i t)) z := by
  have h := interpret_endpoint (stageD base l f g t z) (pivotQ base l f g t z)
    (FFTChainDFT.PhysicalPhase.phase_four f _ _ z) (viewAt f g t z)
    (fun op => rawRun I base l hbase hH hOk op f)
    (fun op hop y => rawRun_main I base l hbase hH hOk op
      (Schedule.valid_ops op (by rwa [←code_eq_schedule])) f y g t z) v i
  simpa only [code_eq_schedule,stages_eq_target,viewAt_get,rawList] using h

include hbase hOk in
 theorem raw_fresh_endpoint (f : ℕ)
    (v : Data (LC (Fin 17) H l) (PRole (Orth (LC (Fin 17) H l)) T Sl C) f)
    (g : Orth (LC (Fin 17) H l)) (k : Fin 36) (s : Sl) :
    rawList I base l hbase hH hOk Schedule.code f v (freshR g k s) =
      matAct f (bankResidual I l hH k g s) (v (freshR g k s)) := by
  rw [rawList_fresh I base l hbase hH hOk Schedule.code Schedule.valid_ops,native_bank_once,pow_one]
end Geometry
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.raw_main_endpoint
#print axioms OAI.PowerSaving.ChainNet.raw_fresh_endpoint
