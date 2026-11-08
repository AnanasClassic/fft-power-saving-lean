import Submission.TransportedQuery

/-! The inverse query is the cube when Q² is an involution. -/
noncomputable section
namespace FFTChainDFT.ArrayNormalizer
variable {ι : Type*}

def inverseQuery (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := Q.comp (Q.comp Q)

theorem query_fourth (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a, Q (Q a) = translate σ a) (a : ι → ℂ) :
    Q (Q (Q (Q a))) = a := by
  rw [hQ2, hQ2, translate_translate σ hσ]

theorem inverseQuery_left (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a, Q (Q a) = translate σ a) (a : ι → ℂ) :
    inverseQuery Q (Q a) = a := query_fourth σ hσ Q hQ2 a

theorem inverseQuery_right (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a, Q (Q a) = translate σ a) (a : ι → ℂ) :
    Q (inverseQuery Q a) = a := query_fourth σ hσ Q hQ2 a

theorem inverseQuery_square (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a, Q (Q a) = translate σ a) (a : ι → ℂ) :
    inverseQuery Q (inverseQuery Q a) = translate σ a := by
  change Q (Q (Q (Q (Q (Q a))))) = _
  rw [query_fourth σ hσ Q hQ2, hQ2]

/-- The stated inverse-query identity on arbitrary independent arrays. -/
theorem transported_inverse_query_involution (σ : ι → ι)
    (hσ : ∀ i, σ (σ i) = i) (Q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hQ2 : ∀ a, Q (Q a) = translate σ a)
    (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer σ (applyQuery (inverseQuery Q)
      (normalizer σ (applyQuery (inverseQuery Q) v))) = v :=
  transported_query_involution σ hσ (inverseQuery Q)
    (inverseQuery_square σ hσ Q hQ2) v

end FFTChainDFT.ArrayNormalizer
