import Mathlib

/-!
# Algebraic core of the paired whole-array normalizer

This module contains universal field identities only. They do not assume any
special values for the input components. For the FFT application the indeterminate
`p` stands for a commuting square-one *operator*, and the pair stands for two
independent data arrays. An additional Lean bridge from this commutative-field
model to the actual array-endomorphism algebra remains to be constructed.

All statements below are ordinary theorems, with no `sorry`, `admit`, or new axioms.
This source has NOT been compiled in the present environment.
-/

namespace FFTChainDFT
namespace Normalizer

variable {R : Type*} [Field R] [CharZero R]

/-- Apply an involutive address translation to the second of two roles. -/
def shiftSecond (p : R) (v : R × R) : R × R := (v.1, p * v.2)

/-- A rational, pointwise Hadamard mix of two independent roles. -/
def hadamard (v : R × R) : R × R := (v.1 + v.2, v.1 - v.2)

/-- Inverse rational Hadamard mix; one division by the fixed constant two. -/
def hadamardInv (v : R × R) : R × R :=
  ((v.1 + v.2) / 2, (v.1 - v.2) / 2)

/-- Chronological gates: translation, inverse mix, translation, mix. -/
def normalizer (p : R) (v : R × R) : R × R :=
  hadamard (shiftSecond p (hadamardInv (shiftSecond p v)))

/-- Closed-form expression `(I+J)/2 + (I-J)*P/2`. -/
def closedForm (p : R) (v : R × R) : R × R :=
  (((1 + p) * v.1 - (1 - p) * v.2) / 2,
   ((1 - p) * v.1 + (1 + p) * v.2) / 2)

/-- The elementary scaling of each independent role. -/
def scalePair (q : R) (v : R × R) : R × R :=
  (q * v.1, q * v.2)

/-- The inverse mixing gate really is inverse (left composition). -/
theorem hadamardInv_hadamard (v : R × R) :
    hadamardInv (hadamard v) = v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [hadamardInv, hadamard]
    ring
  · dsimp [hadamardInv, hadamard]
    ring

/-- The inverse mixing gate really is inverse (right composition). -/
theorem hadamard_hadamardInv (v : R × R) :
    hadamard (hadamardInv v) = v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [hadamardInv, hadamard]
    ring
  · dsimp [hadamardInv, hadamard]
    ring

/-- Precise realization of the claimed two-array map for `p²=1`. -/
theorem normalizer_eq_closedForm (p : R) (v : R × R) (hp : p ^ 2 = 1) :
    normalizer p v = closedForm p v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [normalizer, closedForm, hadamard, hadamardInv, shiftSecond]
    linear_combination (-y / 2) * hp
  · dsimp [normalizer, closedForm, hadamard, hadamardInv, shiftSecond]
    linear_combination (y / 2) * hp

/-- The closed-form map squares to multiplication by `p`, for `p²=1`. -/
theorem closedForm_square (p : R) (v : R × R) (hp : p ^ 2 = 1) :
    closedForm p (closedForm p v) = scalePair p v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [closedForm, scalePair]
    linear_combination (y / 2) * hp
  · dsimp [closedForm, scalePair]
    linear_combination (-x / 2) * hp

/-- Operator identity `Λ² = P·I₂`, expressed on two independent inputs. -/
theorem normalizer_square (p : R) (v : R × R) (hp : p ^ 2 = 1) :
    normalizer p (normalizer p v) = scalePair p v := by
  calc
    normalizer p (normalizer p v) = closedForm p (normalizer p v) :=
      normalizer_eq_closedForm p (normalizer p v) hp
    _ = closedForm p (closedForm p v) := by
      rw [normalizer_eq_closedForm p v hp]
    _ = scalePair p v := closedForm_square p v hp

/-- Pointwise mixing commutes with a common scalar `q`. -/
theorem normalizer_scale_commutes (p q : R) (v : R × R) :
    normalizer p (scalePair q v) = scalePair q (normalizer p v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [normalizer, scalePair, hadamard, hadamardInv, shiftSecond]
    ring
  · dsimp [normalizer, scalePair, hadamard, hadamardInv, shiftSecond]
    ring

/-- Common scalings compose by multiplying their scalars. -/
theorem scalePair_twice (q : R) (v : R × R) :
    scalePair q (scalePair q v) = scalePair (q ^ 2) v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [scalePair]
    ring
  · dsimp [scalePair]
    ring

/--
The transported query `Λ Q⁻¹` is involutive whenever `Q⁻² = P` and `P² = I`.
Here `q` denotes the scalar image of `Q⁻¹`. The array-level version needs a
homomorphism from the operator algebra into this model.
-/
theorem transported_query_square (p q : R) (v : R × R)
    (hp : p ^ 2 = 1) (hq : q ^ 2 = p) :
    normalizer p (scalePair q (normalizer p (scalePair q v))) = v := by
  calc
    normalizer p (scalePair q (normalizer p (scalePair q v)))
        = normalizer p (normalizer p (scalePair q (scalePair q v))) := by
          rw [← normalizer_scale_commutes p q (scalePair q v)]
    _ = normalizer p (normalizer p (scalePair (q ^ 2) v)) := by
          rw [scalePair_twice]
    _ = scalePair p (scalePair (q ^ 2) v) := normalizer_square p _ hp
    _ = scalePair p (scalePair p v) := by rw [hq]
    _ = scalePair (p ^ 2) v := scalePair_twice p v
    _ = v := by
          rw [hp]
          cases v
          simp [scalePair]

end Normalizer
end FFTChainDFT
