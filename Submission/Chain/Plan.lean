import Submission.Chain.ScheduleCost
import Mathlib.Tactic
namespace FFTChainDFT.Chain.Schedule
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def ValidOp : Op → Prop
  | .full _ a b => (a=1 ∧ b=0) ∨ (a=21 ∧ b=20)
  | .idle _ ks => ks.Nodup ∧ 0<ks.length ∧ ks.length≤8
  | .query a b | .swap a b | .had a b | .hadInv a b => a≠b
  | _ => True
instance (op : Op) : Decidable (ValidOp op) := by cases op <;> unfold ValidOp <;> infer_instance

theorem valid_ops : ∀ op ∈ code, ValidOp op := by decide +kernel

def fullID (k : Fin 18) (a : Fin 40) : Fin 36 :=
  ⟨(2*k.val+a.val/20)%36,Nat.mod_lt _ (by decide)⟩

theorem full_id_values (k : Fin 18) (a b : Fin 40)
    (h : ValidOp (.full k a b)) :
    ((fullID k a).val/2=k.val) ∧
      ((fullID k a).val%2=0 ∧ a=1 ∧ b=0 ∨ (fullID k a).val%2=1 ∧ a=21 ∧ b=20) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> fin_cases k <;> decide
end FFTChainDFT.Chain.Schedule
#print axioms FFTChainDFT.Chain.Schedule.valid_ops
#print axioms FFTChainDFT.Chain.Schedule.full_id_values
