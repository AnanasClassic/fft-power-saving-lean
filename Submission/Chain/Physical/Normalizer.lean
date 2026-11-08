import Submission.Work.GFrame.Engine.Letters
import Submission.Chain.Physical.LinearNormalizer
/-! A concrete four-letter GWord for the rational two-array normalizer.
All statements quantify over every tensor width and arbitrary complex data.
The only letters are rational mixing matrices and free address shifts. -/
namespace FFTChainDFT.PhysicalNormalizer
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Matrix
noncomputable section

section Physical
variable {α : Type*} [Fintype α] [DecidableEq α]
/-- Linear action of a physical label matrix at tensor width f. -/
def matLinear (f : ℕ) (M : CMat α) : (Sky α f → ℂ) →ₗ[ℂ] (Sky α f → ℂ) where
  toFun := matAct f M
  map_add' := Matrix.mulVec_add _
  map_smul' := fun c v => by
    change (digitProd (fun _ : Fin f => M)).mulVec (c • v) = c • (digitProd (fun _ : Fin f => M)).mulVec v
    exact Matrix.mulVec_smul _ _ _

 theorem shiftLinear_square (f : ℕ) (z : Space α) (v : Sky α f → ℂ) :
    matLinear f (shift z) (matLinear f (shift z) v)=v := by
  change matAct f (shift z) (matAct f (shift z) v)=v
  rw [matAct_mul,shift_sq,matAct_one]

def H : Matrix Bool Bool ℚ := fun r s => if r && s then -1 else 1
def HI : Matrix Bool Bool ℚ := fun r s => H r s / 2

def word (z : Space α) : GWord α Bool :=
  [.old (.shift true z), .old (.localM HI), .old (.shift true z), .old (.localM H)]
def unpack (f : ℕ) (v : Data α Bool f) : (Sky α f → ℂ) × (Sky α f → ℂ) := (v false,v true)

 theorem word_free (z : Space α) (φ : ℕ → ℝ) : (word z).costR φ=0 := by
  simp [word,GWord.costR,GMove.costR,GMove.shadow,BMove.costR,BMove.rk?]
 theorem word_proper (z : Space α) : (word z).Proper (Fintype.card α) := by
  intro mv hm
  simp only [word,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl <;> trivial

 theorem unpack_H (f : ℕ) (v : Data α Bool f) :
    unpack f (point f (actPoint H) v) = mix (unpack f v) := by
  apply Prod.ext <;> funext i <;>
    simp [unpack,mix,point,actPoint,H,Fintype.sum_bool,sub_eq_add_neg] <;> ring

 theorem unpack_HI (f : ℕ) (v : Data α Bool f) :
    unpack f (point f (actPoint HI) v) = mixInv (unpack f v) := by
  apply Prod.ext <;> funext i <;>
    simp [unpack,mixInv,point,actPoint,HI,H,Fintype.sum_bool] <;> ring

 theorem unpack_shift (f : ℕ) (z : Space α) (v : Data α Bool f) :
    unpack f (roleAct f true (shift z) v) = second (matLinear f (shift z)) (unpack f v) := by
  rfl

/-- Actual whole-array physical realization; not only a scalar matrix identity. -/
 theorem word_action (f : ℕ) (z : Space α) (v : Data α Bool f) :
    unpack f (gwalk f (word z) v) = normalizer (matLinear f (shift z)) (unpack f v) := by
  simp only [word,gwalk_cons,gwalk_nil,GMove.act,BMove.act,
    unpack_H,unpack_shift,unpack_HI,normalizer]

 theorem word_square (f : ℕ) (z : Space α) (v : Data α Bool f) :
    unpack f (gwalk f (word z) (gwalk f (word z) v)) =
      both (matLinear f (shift z)) (unpack f v) := by
  rw [word_action,word_action]
  exact square _ (shiftLinear_square f z) _
end Physical
end
end FFTChainDFT.PhysicalNormalizer
#print axioms FFTChainDFT.PhysicalNormalizer.word_action
#print axioms FFTChainDFT.PhysicalNormalizer.word_square
#print axioms FFTChainDFT.PhysicalNormalizer.transported_square
