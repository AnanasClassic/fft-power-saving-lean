import Mathlib

/-!
# A genuine two-array implementation, at arbitrary index type

For any index set `ι` and involutive address permutation `σ`, the word

    shift(second), inverse Hadamard, shift(second), Hadamard

acts on TWO ARBITRARY COMPLEX ARRAYS. It uses only rational mixes and
address shifts. The normalizer is not built by tensoring a one-column
complex scalar gate; the mixes apply *once per complete array address*.

This is the operator-level `Λ² = P·I₂` identity that can be instantiated at
every tensor width. To obtain the exact-DFT result it must still be connected
to the `OAI.PowerSaving` `Data`/`point`/`matAct` implementation and its charged
RAM semantics. No such bridge is claimed here.

This source has NOT yet been compiled in the present environment.
-/

namespace FFTChainDFT
namespace ArrayNormalizer

variable {ι : Type*}

/-- Address translation by `σ`, on any complex-valued array. -/
def translate (σ : ι → ι) (a : ι → ℂ) : ι → ℂ := fun i => a (σ i)

/-- Translate the second independent array, leaving the first untouched. -/
def shiftSecond (σ : ι → ι) (v : (ι → ℂ) × (ι → ℂ)) :
    (ι → ℂ) × (ι → ℂ) := (v.1, translate σ v.2)

/-- One ordinary rational mixing pass. -/
def hadamard (v : (ι → ℂ) × (ι → ℂ)) :
    (ι → ℂ) × (ι → ℂ) :=
  (fun i => v.1 i + v.2 i, fun i => v.1 i - v.2 i)

/-- Inverse mixing pass, still over two arbitrary complex arrays. -/
def hadamardInv (v : (ι → ℂ) × (ι → ℂ)) :
    (ι → ℂ) × (ι → ℂ) :=
  (fun i => (v.1 i + v.2 i) / 2, fun i => (v.1 i - v.2 i) / 2)

/-- The complete word of two full-array shifts and two rational mixing passes. -/
def normalizer (σ : ι → ι) (v : (ι → ℂ) × (ι → ℂ)) :
    (ι → ℂ) × (ι → ℂ) :=
  hadamard (shiftSecond σ (hadamardInv (shiftSecond σ v)))

/-- A closed-form expression with the translated input arrays. -/
def closedForm (σ : ι → ι) (v : (ι → ℂ) × (ι → ℂ)) :
    (ι → ℂ) × (ι → ℂ) :=
  (fun i => (v.1 i + v.1 (σ i) - v.2 i + v.2 (σ i)) / 2,
   fun i => (v.1 i - v.1 (σ i) + v.2 i + v.2 (σ i)) / 2)

/-- The address translation is involutive whenever `σ² = id`. -/
theorem translate_translate (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (v : ι → ℂ) : translate σ (translate σ v) = v := by
  funext i
  simp [translate, hσ i]

/-- The ordinary mixing passes are inverses on *all* complex inputs. -/
theorem hadamardInv_hadamard (v : (ι → ℂ) × (ι → ℂ)) :
    hadamardInv (hadamard v) = v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · funext i
    dsimp [hadamard, hadamardInv]
    ring
  · funext i
    dsimp [hadamard, hadamardInv]
    ring

/-- Exact operator expression of the four-gate normalizer on arbitrary arrays. -/
theorem normalizer_eq_closedForm (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (v : (ι → ℂ) × (ι → ℂ)) : normalizer σ v = closedForm σ v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · funext i
    dsimp [normalizer, closedForm, hadamard, hadamardInv, shiftSecond, translate]
    rw [hσ i] <;> ring
  · funext i
    dsimp [normalizer, closedForm, hadamard, hadamardInv, shiftSecond, translate]
    rw [hσ i] <;> ring

/-- Closed-form normalizer squared is the address translation on each copy. -/
theorem closedForm_square (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (v : (ι → ℂ) × (ι → ℂ)) :
    closedForm σ (closedForm σ v) = (translate σ v.1, translate σ v.2) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · funext i
    dsimp [closedForm, translate]
    simp only [hσ] <;> ring
  · funext i
    dsimp [closedForm, translate]
    simp only [hσ] <;> ring

/-- `Λ² = P·I₂` for every index type, with no input/scratch assumptions. -/
theorem normalizer_square (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer σ (normalizer σ v) = (translate σ v.1, translate σ v.2) := by
  calc
    normalizer σ (normalizer σ v) = closedForm σ (normalizer σ v) :=
      normalizer_eq_closedForm σ hσ (normalizer σ v)
    _ = closedForm σ (closedForm σ v) := by
      rw [normalizer_eq_closedForm σ hσ v]
    _ = (translate σ v.1, translate σ v.2) := closedForm_square σ hσ v

end ArrayNormalizer
end FFTChainDFT
