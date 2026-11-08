import Submission.Chain.Physical.Normalizer
import Submission.Chain.Physical.Phase
import Submission.Chain.Physical.Thin
/-! Physical normalizer and inverse-query identities at every tensor width.
The query is realized by two rank-one blocks, with free shifts; the four-letter
normalizer is free. Both complex arrays are arbitrary and independent. -/
namespace FFTChainDFT.PhysicalNormalizer
open OAI.PowerSaving OAI.PowerSaving.CB OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.P4L Matrix
noncomputable section
variable {α : Type} [Fintype α] [DecidableEq α]

theorem single_frame_delta (A : OBase α) (p : α) : frame A {p} = delta (A.v p) := by
  have h := frame_ins A ∅ p (Finset.notMem_empty p)
  simpa only [Finset.insert_empty,frame_zero,Matrix.mul_one] using h

theorem single_inverse_square (A : OBase α) (p : α) :
    unframe A {p} * unframe A {p} = shift (A.v p) := by
  calc
    _ = wrap (fun x => fr A {p} x * fr A {p} x) := by
      simp only [unframe_eq_wrap,wrap_mul]
      congr 1
      funext x
      simp only [fr_single_inv]
      calc
        _ = (fr A {p} x * fr A {p} x) *
            (sign (dot (A.v p) x) * sign (dot (A.v p) x)) := by ring
        _ = _ := by rw [sign_sq,mul_one]
    _ = frame A {p} * frame A {p} := by simp only [frame_eq_wrap,wrap_mul]
    _ = shift (A.v p) := by simpa only [single_frame_delta] using delta_sq (A.v p) (A.self p)

theorem single_inverse_four (A : OBase α) (p : α) :
    unframe A {p} * unframe A {p} * unframe A {p} * unframe A {p} = 1 := by
  calc
    _ = (unframe A {p} * unframe A {p}) * (unframe A {p} * unframe A {p}) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by simp only [single_inverse_square,shift_sq]

theorem linear_inverse_square (f : ℕ) (A : OBase α) (p : α) :
    (matLinear f (unframe A {p})).comp (matLinear f (unframe A {p})) = matLinear f (shift (A.v p)) := by
  apply LinearMap.ext
  intro v
  change matAct f (unframe A {p}) (matAct f (unframe A {p}) v) = matAct f (shift (A.v p)) v
  rw [matAct_mul,single_inverse_square]

theorem linear_inverse_four (f : ℕ) (A : OBase α) (p : α) (v : Sky α f → ℂ) :
    matLinear f (unframe A {p}) (matLinear f (unframe A {p})
      (matLinear f (unframe A {p}) (matLinear f (unframe A {p}) v))) = v := by
  change ((matLinear f (unframe A {p})).comp (matLinear f (unframe A {p})))
    (((matLinear f (unframe A {p})).comp (matLinear f (unframe A {p}))) v) = v
  simp only [linear_inverse_square]
  exact shiftLinear_square f (A.v p) v

/-- The actual port matrices instantiate the transported-query identity. -/
theorem actual_transported_square (f : ℕ) (A : OBase α) (p : α)
    (v : (Sky α f → ℂ) × (Sky α f → ℂ)) :
    normalizer (matLinear f (shift (A.v p))) (both (matLinear f (unframe A {p}))
      (normalizer (matLinear f (shift (A.v p))) (both (matLinear f (unframe A {p})) v))) = v := by
  simpa only [linear_inverse_square] using
    transported_square (matLinear f (unframe A {p})) (linear_inverse_four f A p) v

def queryData (f : ℕ) (A : OBase α) (p : α) (v : Data α Bool f) : Data α Bool f :=
  fun b => matAct f (unframe A {p}) (v b)
def transportedData (f : ℕ) (A : OBase α) (p : α) (v : Data α Bool f) : Data α Bool f :=
  gwalk f (word (A.v p)) (queryData f A p v)

theorem unpack_query (f : ℕ) (A : OBase α) (p : α) (v : Data α Bool f) :
    unpack f (queryData f A p v) = both (matLinear f (unframe A {p})) (unpack f v) := rfl

theorem transported_data_square (f : ℕ) (A : OBase α) (p : α) (v : Data α Bool f) :
    unpack f (transportedData f A p (transportedData f A p v)) = unpack f v := by
  simp only [transportedData,word_action,unpack_query]
  exact actual_transported_square f A p (unpack f v)

/-- The physical query on both independent arrays costs exactly two rank-one calls. -/
theorem query_route (A : OBase α) (p : α) (h2 : 1<Fintype.card α) :
    ORoute (fun f => queryData f A p) (fun φ => 2*bcost φ 1) := by
  have h := ORoute.reach (ρ := Bool) (fun _ => (1 : CMat α)) (fun _ => 1)
    (fun _ => unframe A {p}) (fun _ => Matrix.mul_one 1) (fun _ φ => bcost φ 1)
    (fun _ => OAI.PowerSaving.ChainNet.greach_unframe_single A p h2)
  exact h.cast (fun f v => by funext b; simp only [Matrix.mul_one,queryData])
    (fun φ => by simp [Fintype.sum_bool,two_mul])

/-- A finite proper GWord, with all costs accounted for, realizes Λ Q⁻¹. -/
theorem transported_route (A : OBase α) (p : α) (h2 : 1<Fintype.card α) :
    ORoute (fun f => transportedData f A p) (fun φ => 2*bcost φ 1) := by
  have hn : ORoute (fun f v => gwalk f (word (A.v p)) v) (fun _ => 0) :=
    ⟨word (A.v p),word_proper (A.v p),word_free (A.v p),fun _ _ => rfl⟩
  exact ((query_route A p h2).trans hn).cast (fun _ _ => rfl) (fun _ => add_zero _)

 theorem unpack_injective (f : ℕ) : Function.Injective (unpack (α := α) f) := by
  intro v w h
  funext b
  cases b
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- A concrete finite-program existence statement in the trusted word language,
including proper ranks, exact paid cost and the all-data involution contract. -/
theorem transported_program_exists (A : OBase α) (p : α) (h2 : 1<Fintype.card α) :
    ∃ wd : GWord α Bool, wd.Proper (Fintype.card α) ∧
      (∀ φ, wd.costR φ = 2*bcost φ 1) ∧
      ∀ f v, gwalk f wd (gwalk f wd v) = v := by
  obtain ⟨wd,hp,hc,hw⟩ := transported_route A p h2
  refine ⟨wd,hp,hc,?_⟩
  intro f v
  rw [hw,hw]
  apply unpack_injective f
  exact transported_data_square f A p v
end
end FFTChainDFT.PhysicalNormalizer
#print axioms FFTChainDFT.PhysicalNormalizer.actual_transported_square
#print axioms FFTChainDFT.PhysicalNormalizer.transported_data_square
#print axioms FFTChainDFT.PhysicalNormalizer.transported_route

#print axioms FFTChainDFT.PhysicalNormalizer.transported_program_exists
