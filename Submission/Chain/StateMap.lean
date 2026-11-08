import Submission.Chain.Common
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
namespace FFTChainDFT.Chain.State
variable {R S : Type*}
def map (f : R → S) (u : State R) : State S := ⟨f u.r00, f u.r01, f u.r02, f u.r03, f u.r04, f u.r05, f u.r06, f u.r07, f u.r08, f u.r09, f u.r10, f u.r11, f u.r12, f u.r13, f u.r14, f u.r15, f u.r16, f u.r17, f u.r18, f u.r19, f u.r20, f u.r21, f u.r22, f u.r23, f u.r24, f u.r25, f u.r26, f u.r27, f u.r28, f u.r29, f u.r30, f u.r31, f u.r32, f u.r33, f u.r34, f u.r35, f u.r36, f u.r37, f u.r38, f u.r39⟩
theorem map_get (f : R → S) (u : State R) (i : Fin 40) :
  (map f u).get i = f (u.get i) := by fin_cases i <;> rfl
theorem map_set (f : R → S) (u : State R) (i : Fin 40) (x : R) :
  map f (u.set i x) = (map f u).set i (f x) := by fin_cases i <;> rfl
def ofFn (f : Fin 40 → R) : State R := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31, f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39⟩
theorem get_ofFn (f : Fin 40 → R) (i : Fin 40) : (ofFn f).get i=f i := by
  fin_cases i <;> rfl
end FFTChainDFT.Chain.State
