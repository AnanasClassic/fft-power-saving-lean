import Submission.Chain.StateGet
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
namespace FFTChainDFT.Chain.GateAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

def row (a j : Fin 40) : ℚ := if j=a then 1 else 0
def addMat (a b : Fin 40) (c : ℚ) : Matrix (Fin 40) (Fin 40) ℚ :=
  fun i j => row i j + (if i=a then c*row b j else 0)
def scaleMat (a : Fin 40) (c : ℚ) : Matrix (Fin 40) (Fin 40) ℚ :=
  fun i j => if i=a then c*row a j else row i j

variable {R : Type*} [Field R] [CharZero R]
theorem cast_row (a j : Fin 40) : ((row a j : ℚ) : R) = if j=a then 1 else 0 := by
  by_cases h : j=a <;> simp [row,h]

theorem row_eval (u : State R) (a : Fin 40) :
    ∑ j, ((row a j : ℚ) : R)*u.get j = u.get a := by
  simp [cast_row,ite_mul,Finset.sum_ite_eq']

theorem add_eval (d : Fin 18 → R) (q : R) (u : State R) (a b i : Fin 40) (c : ℚ) :
    (∑ j, ((addMat a b c i j : ℚ) : R)*u.get j) = (Op.eval d q (.add a b c) u).get i := by
  by_cases hi : i=a
  · subst i
    simp only [addMat,ite_true,ite_false,if_pos rfl,Rat.cast_add,Rat.cast_mul,add_mul,mul_assoc,Finset.sum_add_distrib,
      Op.eval,State.get_set_same]
    rw [←Finset.mul_sum,row_eval,row_eval]
  · simp only [addMat,ite_true,ite_false,if_neg hi,Rat.cast_add,Rat.cast_zero,add_zero,row_eval,
      Op.eval,State.get_set_ne _ _ _ _ hi]

theorem scale_eval (d : Fin 18 → R) (q : R) (u : State R) (a i : Fin 40) (c : ℚ) :
    (∑ j, ((scaleMat a c i j : ℚ) : R)*u.get j) = (Op.eval d q (.scale a c) u).get i := by
  by_cases hi : i=a
  · subst i
    simp only [scaleMat,ite_true,ite_false,if_pos rfl,Rat.cast_mul,mul_assoc,Op.eval,State.get_set_same]
    rw [←Finset.mul_sum,row_eval]
  · simp only [scaleMat,ite_true,ite_false,if_neg hi,row_eval,Op.eval,State.get_set_ne _ _ _ _ hi]

 theorem had_as_gates (d : Fin 18 → R) (q : R) (a b : Fin 40) (h : a≠b) (u : State R) :
    Op.eval d q (.add b a 1) (Op.eval d q (.scale b (-2)) (Op.eval d q (.add a b 1) u)) =
      Op.eval d q (.had a b) u := by
  apply State.ext_get
  intro i
  by_cases ha : i=a
  · subst i
    simp [Op.eval,State.get_set_same,State.get_set_ne,h,Ne.symm h] <;> ring
  · by_cases hb : i=b
    · subst i
      simp [Op.eval,State.get_set_same,State.get_set_ne,h,Ne.symm h] <;> ring
    · simp [Op.eval,State.get_set_same,State.get_set_ne,ha,hb]

 theorem hadInv_as_gates (d : Fin 18 → R) (q : R) (a b : Fin 40) (h : a≠b) (u : State R) :
    Op.eval d q (.scale b (1/2)) (Op.eval d q (.scale a (1/2)) (Op.eval d q (.had a b) u)) =
      Op.eval d q (.hadInv a b) u := by
  apply State.ext_get
  intro i
  by_cases ha : i=a
  · subst i
    simp [Op.eval,State.get_set_same,State.get_set_ne,h,Ne.symm h] <;> ring
  · by_cases hb : i=b
    · subst i
      simp [Op.eval,State.get_set_same,State.get_set_ne,h,Ne.symm h] <;> ring
    · simp [Op.eval,State.get_set_same,State.get_set_ne,ha,hb]

 theorem swap_as_gates (d : Fin 18 → R) (q : R) (a b : Fin 40) (h : a≠b) (u : State R) :
    Op.eval d q (.add a b (-1)) (Op.eval d q (.add b a 1)
      (Op.eval d q (.scale b (-1)) (Op.eval d q (.add a b 1) u))) =
      Op.eval d q (.swap a b) u := by
  apply State.ext_get
  intro i
  by_cases ha : i=a
  · subst i
    simp [Op.eval,State.get_set_same,State.get_set_ne,h,Ne.symm h] <;> ring
  · by_cases hb : i=b
    · subst i
      simp [Op.eval,State.get_set_same,State.get_set_ne,h,Ne.symm h] <;> ring
    · simp [Op.eval,State.get_set_same,State.get_set_ne,ha,hb]
end
end FFTChainDFT.Chain.GateAlgebra
#print axioms FFTChainDFT.Chain.GateAlgebra.add_eval
#print axioms FFTChainDFT.Chain.GateAlgebra.had_as_gates
