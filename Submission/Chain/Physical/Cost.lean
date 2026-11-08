import Submission.Chain.Physical.RawCompiler
import Submission.Native.Provider
import Submission.InventoryLink
import Submission.Work.BlockApply.Exact
/-! Exact invoice for the physical opcode interpretation. The proof prices
the actual schedule, including every whole idle and rank-one query. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
section Generic
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
  {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (l : H)

def tagPrice (φ : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r=0 then I.cost φ else (Fintype.card T : ℝ)*bcost φ r

def portPrice (φ : ℕ → ℝ) : ℝ :=
  6*bcost φ 1 + ((List.range 8).map fun j => 4*bcost φ (8*(j+1))).sum

theorem opcode_tagPrice (op : Op) (h : Schedule.ValidOp op) (φ : ℕ → ℝ) :
    opcodePrice I l op φ = (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*
      ((Schedule.billTag op).map (tagPrice I φ)).sum := by
  cases op with
  | idle a ks =>
    have hn : 8*ks.length≠0 := Nat.mul_ne_zero (by decide) (Nat.ne_of_gt h.2.1)
    simp only [opcodePrice,Schedule.billTag,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,tagPrice,if_neg hn]
    ring
  | full k a b => simp only [opcodePrice,Schedule.billTag,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      tagPrice,ite_true,add_zero]
  | query a b =>
    simp only [opcodePrice,Schedule.billTag,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      tagPrice,show (1:ℕ)≠0 by decide,ite_false,add_zero]
    ring
  | add a b c => simp only [opcodePrice,Schedule.billTag,List.map_nil,List.sum_nil,mul_zero]
  | scale a c => simp only [opcodePrice,Schedule.billTag,List.map_nil,List.sum_nil,mul_zero]
  | swap a b => simp only [opcodePrice,Schedule.billTag,List.map_nil,List.sum_nil,mul_zero]
  | shift a => simp only [opcodePrice,Schedule.billTag,List.map_nil,List.sum_nil,mul_zero]
  | had a b => simp only [opcodePrice,Schedule.billTag,List.map_nil,List.sum_nil,mul_zero]
  | hadInv a b => simp only [opcodePrice,Schedule.billTag,List.map_nil,List.sum_nil,mul_zero]

theorem schedule_price (φ : ℕ → ℝ) :
    (Schedule.code.map (fun op => opcodePrice I l op φ)).sum =
      (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*
        (36*I.cost φ + (Fintype.card T : ℝ)*portPrice φ) := by
  have hs (ops : List Op) (h : ∀ op∈ops, Schedule.ValidOp op) :
      (ops.map (fun op => opcodePrice I l op φ)).sum =
        (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*
          (((ops.flatMap Schedule.billTag).map (tagPrice I φ)).sum) := by
    induction ops with
    | nil => simp
    | cons a ops ih =>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append]
      rw [opcode_tagPrice I l a (h a List.mem_cons_self),ih (fun op hop => h op (List.mem_cons_of_mem a hop))]
      ring
  rw [hs Schedule.code Schedule.valid_ops]
  change _ * (Schedule.tags.map (tagPrice I φ)).sum = _
  rw [Schedule.tag_sum]
  have hz : tagPrice I φ 0=I.cost φ := by simp only [tagPrice,ite_true]
  have h1 : tagPrice I φ 1=(Fintype.card T : ℝ)*bcost φ 1 := by simp only [tagPrice,show (1:ℕ)≠0 by decide,ite_false]
  have hn (j : ℕ) : tagPrice I φ (8*(j+1))=(Fintype.card T : ℝ)*bcost φ (8*(j+1)) := by
    simp only [tagPrice,show 8*(j+1)≠0 by omega,ite_false]
  simp only [hz,h1,hn,nsmul_eq_mul,Nat.cast_ofNat]
  have hf : ((List.range 8).map fun j => 4*((Fintype.card T : ℝ)*bcost φ (8*(j+1)))).sum =
      (Fintype.card T : ℝ)*((List.range 8).map fun j => 4*bcost φ (8*(j+1))).sum := by
    simp_rw [show ∀ j, 4*((Fintype.card T : ℝ)*bcost φ (8*(j+1))) =
      (Fintype.card T : ℝ)*(4*bcost φ (8*(j+1))) by intro j; ring]
    exact List.sum_map_mul_left (List.range 8) (fun j => 4*bcost φ (8*(j+1))) (Fintype.card T : ℝ)
  rw [hf]
  unfold portPrice
  ring
end Generic

/-- One actual modified supplier invoice plus the actual non-native calls. -/
theorem native_schedule_price (l : Fin 9) (φ : ℕ → ℝ) :
    (Schedule.code.map (fun op => opcodePrice FFTChainDFT.Native.provider l op φ)).sum =
      (Fintype.card (Orth (LC (Fin 17) (Fin 9) l)) : ℝ)*
        listCost φ FFTChainDFT.Analytic.paidHist := by
  rw [schedule_price,FFTChainDFT.Native.provider_cost]
  congr 1
  simp only [Fintype.card_fin]
  norm_num [portPrice,FFTChainDFT.Native.invPrice,listCost,FFTChainDFT.Analytic.paidHist,List.range_succ,bcost]
  ring
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.native_schedule_price
