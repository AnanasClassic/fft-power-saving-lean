import Submission.Chain.StateMap
namespace FFTChainDFT.Chain.State
set_option maxHeartbeats 4000000
variable {R : Type*}
theorem ext_get (u v : State R) (h : ∀ i, u.get i = v.get i) : u=v := by
  apply State.ext
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6
  · exact h 7
  · exact h 8
  · exact h 9
  · exact h 10
  · exact h 11
  · exact h 12
  · exact h 13
  · exact h 14
  · exact h 15
  · exact h 16
  · exact h 17
  · exact h 18
  · exact h 19
  · exact h 20
  · exact h 21
  · exact h 22
  · exact h 23
  · exact h 24
  · exact h 25
  · exact h 26
  · exact h 27
  · exact h 28
  · exact h 29
  · exact h 30
  · exact h 31
  · exact h 32
  · exact h 33
  · exact h 34
  · exact h 35
  · exact h 36
  · exact h 37
  · exact h 38
  · exact h 39
theorem get_set_same (u : State R) (i : Fin 40) (v : R) : (u.set i v).get i = v := by
  fin_cases i <;> rfl
theorem get_set_ne (u : State R) (i j : Fin 40) (v : R) (h : j ≠ i) :
    (u.set i v).get j = u.get j := by
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h
end FFTChainDFT.Chain.State
