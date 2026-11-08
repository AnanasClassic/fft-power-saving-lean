import Mathlib
namespace FFTChainDFT.PhysicalNormalizer
noncomputable section
section Abstract
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def mix (v : V × V) : V × V := (v.1+v.2,v.1-v.2)
def mixInv (v : V × V) : V × V := ((1/2:ℂ) • (v.1+v.2),(1/2:ℂ) • (v.1-v.2))
def second (P : V →ₗ[ℂ] V) (v : V × V) : V × V := (v.1,P v.2)
def normalizer (P : V →ₗ[ℂ] V) (v : V × V) : V × V := mix (second P (mixInv (second P v)))
def both (P : V →ₗ[ℂ] V) (v : V × V) : V × V := (P v.1,P v.2)
end Abstract

section Arrays
variable {ι : Type*}
 theorem square (P : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hP : ∀ v, P (P v)=v) (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer P (normalizer P v) = both P v := by
  simp only [normalizer,mix,second,mixInv,both,map_add,map_sub,map_smul,hP]
  apply Prod.ext <;> funext i <;>
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> ring

 theorem normalizer_commutes (P R : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (h : ∀ v, P (R v)=R (P v)) (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer P (both R v) = both R (normalizer P v) := by
  simp only [normalizer,mix,second,mixInv,both,map_add,map_sub,map_smul,h]

 theorem transported_square (R : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hR : ∀ v, R (R (R (R v)))=v) (v : (ι → ℂ) × (ι → ℂ)) :
    normalizer (R.comp R) (both R (normalizer (R.comp R) (both R v))) = v := by
  have hp : ∀ w, (R.comp R) ((R.comp R) w)=w := hR
  have hc : ∀ w, (R.comp R) (R w)=R ((R.comp R) w) := fun _ => rfl
  rw [←normalizer_commutes (R.comp R) R hc, square (R.comp R) hp]
  apply Prod.ext <;> exact hR _
end Arrays

end
end FFTChainDFT.PhysicalNormalizer
#print axioms FFTChainDFT.PhysicalNormalizer.square
#print axioms FFTChainDFT.PhysicalNormalizer.transported_square
