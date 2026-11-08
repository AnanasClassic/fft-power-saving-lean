import Submission.Chain.Physical.Stage
import Submission.Chain.StateMap
import Submission.Work.P4L.Basis
/-! The universal rational gate layer, adapted from Kartal's BQ19.View.
Only the finite role type changes; inherited proofs and attribution remain. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW
noncomputable section
section Gates
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
def linMat (M : Matrix (Fin 40) (Fin 40) ℚ) : Matrix (PRole Γ T Sl C) (PRole Γ T Sl C) ℚ := fun r r' =>
  match r, r' with
  | .inl (.inl (g, (i, t))), .inl (.inl (g', (i', t'))) => if g = g' ∧ t = t' then M i i' else 0
  | .inl (.inl _), _ => 0
  | _, .inl (.inl _) => 0
  | r, r' => if r = r' then 1 else 0

lemma linMat_at (M : Matrix (Fin 40) (Fin 40) ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : (Fin 40)) (t : T) :
    point f (actPoint (linMat M)) y (mainR g i t) = ∑ i', ((M i i' : ℚ) : ℂ) • y (mainR g i' t) := by
  funext pt
  simp only [point, actPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∑ x : Γ × (Fin 36 × Sl), ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inl (Sum.inr x)) : ℚ) : ℂ) * y (Sum.inl (Sum.inr x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  have h3 : ∑ x : Γ × C, ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inr (Sum.inl x)) : ℚ) : ℂ) * y (Sum.inr (Sum.inl x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  have h4 : ∑ x : Γ × (Fin 6 × T), ((linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M (mainR g i t)
      (Sum.inr (Sum.inr x)) : ℚ) : ℂ) * y (Sum.inr (Sum.inr x)) pt = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [linMat, mainR]
  rw [h2, h3, h4]
  simp only [add_zero]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single g]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.sum_eq_single t]
    · simp [linMat, mainR]
    · intro t' _ ht'; simp [linMat, mainR, Ne.symm ht']
    · intro h; exact absurd (Finset.mem_univ t) h
  · intro g' _ hg'
    apply Finset.sum_eq_zero
    intro x _
    simp [linMat, mainR, Ne.symm hg']
  · intro h; exact absurd (Finset.mem_univ g) h

/-- a gate layer leaves the other roles unchanged. -/
lemma linMat_other (M : Matrix (Fin 40) (Fin 40) ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (r : PRole Γ T Sl C)
    (hr : ∀ g i t, r ≠ mainR g i t) : point f (actPoint (linMat M)) y r = y r := by
  funext pt
  simp only [point, actPoint]
  rw [Finset.sum_eq_single r]
  · rcases r with ((⟨g, i, t⟩ | h) | c)
    · exact absurd rfl (hr g i t)
    · simp [linMat]
    · simp [linMat]
  · intro r' _ hr'
    rcases r with ((⟨g, i, t⟩ | h) | c)
    · exact absurd rfl (hr g i t)
    · rcases r' with ((⟨g', i', t'⟩ | h') | c') <;> simp [linMat, Ne.symm hr']
    · rcases r' with ((⟨g', i', t'⟩ | h') | c') <;> simp [linMat, Ne.symm hr']
  · intro h; exact absurd (Finset.mem_univ r) h


theorem gate_route (M : Matrix (Fin 40) (Fin 40) ℚ) :
    P4L.ORoute (α := α) (fun f => point f (actPoint (linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) M)))
      (fun _ => 0) := P4L.ORoute.localM _

/-- Read forty independent complex scalars at one Walsh address. -/
def viewAt (f : ℕ) (g : Γ) (t : T) (z : Sky α f) (y : Data α (PRole Γ T Sl C) f) : FFTChainDFT.Chain.State ℂ :=
  FFTChainDFT.Chain.State.ofFn fun i => P4L.walsh f (y (mainR g i t)) z
lemma viewAt_get (f : ℕ) (g : Γ) (t : T) (z : Sky α f) (y : Data α (PRole Γ T Sl C) f) (i : Fin 40) :
    (viewAt f g t z y).get i = P4L.walsh f (y (mainR g i t)) z :=
  FFTChainDFT.Chain.State.get_ofFn _ _

theorem viewAt_gate (M : Matrix (Fin 40) (Fin 40) ℚ) (f : ℕ) (y : Data α (PRole Γ T Sl C) f)
    (g : Γ) (t : T) (z : Sky α f) (i : Fin 40) :
    (viewAt f g t z (point f (actPoint (linMat M)) y)).get i =
      ∑ i', ((M i i' : ℚ) : ℂ) * (viewAt f g t z y).get i' := by
  rw [viewAt_get,linMat_at,P4L.walsh_sum]
  simp only [Finset.sum_apply,P4L.walsh_smul,Pi.smul_apply,smul_eq_mul,viewAt_get]
end Gates
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.gate_route
#print axioms OAI.PowerSaving.ChainNet.viewAt_gate
