import FFTChainDFT.ArrayNormalizer

/-!
# Two-array transported-query involution on arbitrary complex arrays

This extends the normalizer identity from an abstract scalar quotient ring to
actual complex-valued arrays. It assumes only that `Q` is a complex-linear
endomorphism satisfying `Q ∘ Q = P`, with `P` an involutive address translation.
The proof uses no restriction on array inputs. In the exact-DFT construction the
instantiation of `Q` with `matAct f (pivot frame)` and the RAM-operation cost
are additional (unproved here) bridge obligations.

Lean compilation of this module is not yet available in the current container.
-/

namespace FFTChainDFT
namespace ArrayNormalizer

variable {ι : Type*}

/-- The same paired map, written in the additive module language to exploit
    linearity of the arbitrary query operator. -/
def linearClosedForm (σ : ι → ι) (v : (ι → ℂ) × (ι → ℂ)) :
    (ι → ℂ) × (ι → ℂ) :=
  ((1 / 2 : ℂ) • (v.1 + translate σ v.1 - v.2 + translate σ v.2),
   (1 / 2 : ℂ) • (v.1 - translate σ v.1 + v.2 + translate σ v.2))

/-- Converting between pointwise divisions and linear-module operations. -/
theorem linearClosedForm_eq_closedForm (σ : ι → ι)
    (v : (ι → ℂ) × (ι → ℂ)) : linearClosedForm σ v = closedForm σ v := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · funext i
    simp [linearClosedForm, closedForm, translate, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  · funext i
    simp [linearClosedForm, closedForm, translate, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Apply an arbitrary linear query to each of the two independent input arrays. -/
def applyQuery (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (v : (ι → ℂ) × (ι → ℂ)) : (ι → ℂ) × (ι → ℂ) :=
  (Q v.1, Q v.2)

/-- Commutation with a common linear query, provided the query commutes with P. -/
theorem linearClosedForm_commutes (σ : ι → ι)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hcomm : ∀ a : ι → ℂ, Q (translate σ a) = translate σ (Q a))
    (v : (ι → ℂ) × (ι → ℂ)) :
    linearClosedForm σ (applyQuery Q v) = applyQuery Q (linearClosedForm σ v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · dsimp [linearClosedForm, applyQuery]
    simp [map_smul, map_add, map_sub, hcomm]
  · dsimp [linearClosedForm, applyQuery]
    simp [map_smul, map_add, map_sub, hcomm]

/-- `Q²=P` automatically implies `QP=PQ`; no separate commutation axiom. -/
theorem commutes_of_query_square (σ : ι → ι)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a : ι → ℂ, Q (Q a) = translate σ a)
    (a : ι → ℂ) :
    Q (translate σ a) = translate σ (Q a) := by
  calc
    Q (translate σ a) = Q (Q (Q a)) := by rw [← hQ2 a]
    _ = translate σ (Q a) := hQ2 (Q a)

/-- The four-gate normalizer commutes with the native query operator. -/
theorem normalizer_commutes_query (σ : ι → ι)
    (hσ : ∀ i, σ (σ i) = i)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a : ι → ℂ, Q (Q a) = translate σ a)
    (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer σ (applyQuery Q v) = applyQuery Q (normalizer σ v) := by
  calc
    normalizer σ (applyQuery Q v) = closedForm σ (applyQuery Q v) :=
      normalizer_eq_closedForm σ hσ _
    _ = linearClosedForm σ (applyQuery Q v) :=
      (linearClosedForm_eq_closedForm σ (applyQuery Q v)).symm
    _ = applyQuery Q (linearClosedForm σ v) :=
      linearClosedForm_commutes σ Q (commutes_of_query_square σ Q hQ2) v
    _ = applyQuery Q (closedForm σ v) := by rw [linearClosedForm_eq_closedForm]
    _ = applyQuery Q (normalizer σ v) := by rw [normalizer_eq_closedForm σ hσ v]

/-- The query applied twice translates each original independent array. -/
theorem applyQuery_twice (σ : ι → ι)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a : ι → ℂ, Q (Q a) = translate σ a)
    (v : (ι → ℂ) × (ι → ℂ)) :
    applyQuery Q (applyQuery Q v) = (translate σ v.1, translate σ v.2) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · exact hQ2 x
  · exact hQ2 y

/-- **Critical exact-data theorem:** (Λ Q)² = I on any two complex arrays.

    Nothing in this theorem relies on arrays being real/imaginary components,
    on zero helper inputs, or on a fixed tensor width.
-/
theorem transported_query_involution (σ : ι → ι)
    (hσ : ∀ i, σ (σ i) = i)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a : ι → ℂ, Q (Q a) = translate σ a)
    (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer σ (applyQuery Q (normalizer σ (applyQuery Q v))) = v := by
  calc
    normalizer σ (applyQuery Q (normalizer σ (applyQuery Q v)))
        = normalizer σ (normalizer σ (applyQuery Q (applyQuery Q v))) := by
          rw [← normalizer_commutes_query σ hσ Q hQ2 (applyQuery Q v)]
    _ = (translate σ (applyQuery Q (applyQuery Q v)).1,
        translate σ (applyQuery Q (applyQuery Q v)).2) :=
          normalizer_square σ hσ _
    _ = (translate σ (translate σ v.1),
        translate σ (translate σ v.2)) := by
          rw [applyQuery_twice σ Q hQ2 v]
    _ = v := by
          rw [translate_translate σ hσ v.1, translate_translate σ hσ v.2]

end ArrayNormalizer
end FFTChainDFT
