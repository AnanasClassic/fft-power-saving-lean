import Submission.Chain.Physical.Gates
import Submission.Chain.StateGet
import Submission.Work.P4L.View
/-! Forward native-call view, adapted from Kartal BQ19.View to forty roles.
The ratio/cross-frame results and the all-data native operator are inherited.
The pointwise view is evaluated in the complex field used by Chain.endpoint. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
section V
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
def view (f : ℕ) (g : Γ) (t : T) (y : Data α (PRole Γ T Sl C) f) : State (Sky α f → ℂ) :=
  State.ofFn fun i => P4L.walsh f (y (mainR g i t))
lemma view_get (f : ℕ) (g : Γ) (t : T) (y : Data α (PRole Γ T Sl C) f) (i : Fin 40) :
    (view f g t y).get i = P4L.walsh f (y (mainR g i t)) := State.get_ofFn _ _
lemma viewAt_eq (f : ℕ) (g : Γ) (t : T) (z : Sky α f) (y : Data α (PRole Γ T Sl C) f) :
    State.map (fun w => w z) (view f g t y) = viewAt f g t z y := rfl
end V
section CallGet
variable {R : Type*} [CommRing R]
def callF (x y : Fin 40) (d qi : R) (u : State R) : State R :=
  (u.set x (d*u.get x)).set y (d*(u.get y+qi*u.get x))
lemma callF_get_x (x y : (Fin 40)) (hxy : x ≠ y) (d qi : R) (u : State R) : (callF x y d qi u).get x = d * u.get x := by
  unfold callF
  rw [State.get_set_ne _ _ _ _ hxy, State.get_set_same]

lemma callF_get_y (x y : (Fin 40)) (d qi : R) (u : State R) :
    (callF x y d qi u).get y = d * (u.get y + qi * u.get x) := by
  unfold callF
  rw [State.get_set_same]

lemma callF_get_o (x y : (Fin 40)) (d qi : R) (u : State R) (i : (Fin 40)) (hx : i ≠ x) (hy : i ≠ y) :
    (callF x y d qi u).get i = u.get i := by
  unfold callF
  rw [State.get_set_ne _ _ _ _ hy, State.get_set_ne _ _ _ _ hx]

end CallGet
section CallView
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
lemma point_gFk (k : Fin 36) (f : ℕ) (z : Data α (PRole Γ T Sl C) f) (g : Γ) (i : (Fin 40)) (t : T) :
    point f (gFk k) z (mainR g i t)
      = if i = yOf k then z (mainR g (yOf k) t) + z (mainR g (xOf k) t) else z (mainR g i t) := by
  funext pt
  by_cases hy : i = yOf k
  · subst hy
    simp [point, gFk, mainR]
  · simp [point, gFk, mainR, hy]

lemma stT_main (k : Fin 36) (A : Γ → T → OBase α) (sX' sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (g : Γ) (i : (Fin 40)) (t : T) :
    stT (Sl := Sl) (C := C) k A sX' sY' Wn (mainR g i t)
      = if i = xOf k then frame (A g t) sX' else if i = yOf k then frame (A g t) sY' else 1 := rfl

lemma stS'_main (k : Fin 36) (A : Γ → T → OBase α) (sX sY : Finset α) (g : Γ) (i : (Fin 40)) (t : T) :
    stS' (Sl := Sl) (C := C) k A sX sY (mainR g i t)
      = if i = xOf k then unframe (A g t) sX else if i = yOf k then unframe (A g t) sY else 1 := rfl

lemma callF_at (k : Fin 36) (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (i : (Fin 40)) (t : T) :
    multiAct f (stT k A sX' sY' Wn) (point f (gFk k) (multiAct f (stS' k A sX sY) y)) (mainR g i t)
      = if i = xOf k then matAct f (frame (A g t) sX') (matAct f (unframe (A g t) sX) (y (mainR g i t)))
        else if i = yOf k then matAct f (frame (A g t) sY')
          (matAct f (unframe (A g t) sY) (y (mainR g (yOf k) t))
            + matAct f (unframe (A g t) sX) (y (mainR g (xOf k) t)))
        else y (mainR g i t) := by
  have hxy := xOf_ne_yOf k
  by_cases hx : i = xOf k
  · subst hx
    simp [multiAct, point_gFk, stT_main, stS'_main, hxy, Ne.symm hxy]
  · by_cases hy : i = yOf k
    · subst hy
      simp [multiAct, point_gFk, stT_main, stS'_main, hxy, Ne.symm hxy]
    · simp [multiAct, point_gFk, stT_main, stS'_main, hx, hy, Ne.symm hx, Ne.symm hy]

/-- **a forward full call moves the view of every port by `callF`.** -/
theorem view_call_fwd (k : Fin 36) (A : Γ → T → OBase α) (sY Δ : Finset α) (p : α)
    (hΔ : Disjoint (sY ∪ {p}) Δ) (hΔY : Disjoint sY Δ) (hp : Disjoint sY {p}) (Wn : Γ → Sl → CMat α)
    (f : ℕ) (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    view f g t (multiAct f (stT k A (sY ∪ {p} ∪ Δ) (sY ∪ Δ) Wn)
        (point f (gFk k) (multiAct f (stS' k A (sY ∪ {p}) sY) y)))
      = callF (xOf k) (yOf k) (P4L.prodF f (P4L.fr (A g t) Δ)) (P4L.prodF f (fun x => (P4L.fr (A g t) {p} x)⁻¹))
          (view f g t y) := by
  have hxy := xOf_ne_yOf k
  apply State.ext_get
  intro i
  rw [view_get, callF_at]
  by_cases hx : i = xOf k
  · subst hx
    rw [if_pos rfl, callF_get_x _ _ hxy, view_get]
    exact P4L.walsh_ratio f (A g t) (sY ∪ {p}) Δ hΔ _
  · by_cases hy : i = yOf k
    · subst hy
      rw [if_neg hx, if_pos rfl, callF_get_y, view_get, view_get, P4L.matAct_add, P4L.walsh_add,
        P4L.walsh_ratio f (A g t) sY Δ hΔY, P4L.walsh_cross f (A g t) sY Δ p hΔY hp]
      ring
    · rw [if_neg hx, if_neg hy, callF_get_o _ _ _ _ _ i hx hy, view_get]

end CallView
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.view_call_fwd
