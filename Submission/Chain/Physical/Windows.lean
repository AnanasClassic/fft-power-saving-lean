import Submission.Chain.Physical.Elementary
import Submission.Chain.Physical.ArrayQueries
import Submission.Chain.Geometry.Selected
import Submission.Work.P4L.Seg
/-! One physical window per whole idle, and the free P-shift. These operators
act on complete independent arrays and leave all productive helpers unchanged. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section Main
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ]
  [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

def mainSet (a : Fin 40) : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × T)).image fun p => mainR p.1 a p.2

theorem mainSet_mem (a i : Fin 40) (g : Γ) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∈ mainSet a ↔ i=a := by
  rw [mainSet,Finset.mem_image]
  constructor
  · rintro ⟨⟨g',t'⟩,_,h⟩
    simp only [mainR,Sum.inl.injEq,Prod.mk.injEq] at h
    exact h.2.1.symm
  · rintro rfl
    exact ⟨(g,t),Finset.mem_univ _,rfl⟩

theorem card_mainSet (a : Fin 40) : (mainSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) a).card =
    Fintype.card Γ * Fintype.card T := by
  rw [mainSet,Finset.card_image_of_injective _ (fun u v h => by
    simp only [mainR,Sum.inl.injEq,Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2),Finset.card_univ,Fintype.card_prod]

theorem fresh_not_mainSet (a : Fin 40) (g : Γ) (k : Fin 36) (s : Sl) :
    freshR (T := T) (C := C) g k s ∉ mainSet a := by
  rw [mainSet,Finset.mem_image]
  rintro ⟨⟨g',t'⟩,_,h⟩
  cases h

def mainMat (M : Γ → T → CMat α) : PRole Γ T Sl C → CMat α
  | .inl (.inl (g,(_,t))) => M g t
  | _ => 1

def mainWindow (a : Fin 40) (M : Γ → T → CMat α) (f : ℕ) (y : Data α (PRole Γ T Sl C) f) :
    Data α (PRole Γ T Sl C) f :=
  fun r => if r ∈ mainSet a then matAct f (mainMat M r) (y r) else y r

theorem mainWindow_at (a i : Fin 40) (M : Γ → T → CMat α) (f : ℕ)
    (y : Data α (PRole Γ T Sl C) f) (g : Γ) (t : T) :
    mainWindow a M f y (mainR g i t) = if i=a then matAct f (M g t) (y (mainR g i t)) else y (mainR g i t) := by
  simp only [mainWindow,mainSet_mem,mainMat,mainR]

theorem mainWindow_fresh (a : Fin 40) (M : Γ → T → CMat α) (f : ℕ)
    (y : Data α (PRole Γ T Sl C) f) (g : Γ) (k : Fin 36) (s : Sl) :
    mainWindow a M f y (freshR g k s) = y (freshR g k s) := by
  simp only [mainWindow,if_neg (fresh_not_mainSet a g k s)]

theorem mainWindow_route (a : Fin 40) (M : Γ → T → CMat α) (c : (ℕ → ℝ) → ℝ)
    (hM : ∀ g t, GReach 1 (M g t) c) :
    P4L.ORoute (mainWindow (Sl := Sl) (C := C) a M)
      (fun φ => (Fintype.card Γ : ℝ)*(Fintype.card T : ℝ)*c φ) := by
  have h := P4L.ORoute.steps_inv (mainSet (Γ := Γ) (T := T) (Sl := Sl) (C := C) a)
    (fun _ => (1 : CMat α)) (fun _ => 1) (mainMat M) (fun _ _ => Matrix.mul_one 1)
    (fun _ => c) (fun r hr => by
      obtain ⟨⟨g,t⟩,_,rfl⟩ := Finset.mem_image.mp hr
      exact hM g t _ (mainR g a t))
  exact h.cast (fun f y => by funext r; simp only [Matrix.mul_one,mainWindow])
    (fun φ => by simp [card_mainSet,Nat.cast_mul,nsmul_eq_mul,mul_assoc])

theorem greach_frame_set (A : OBase α) (S : Finset α) (hp : 1≤S.card) (hl : S.card<Fintype.card α) :
    GReach 1 (frame A S) (fun φ => bcost φ S.card) := by
  intro ρ _ _ r
  have h := gstep_of_factor r (1 : CMat α) (A.fam S) (OBase.fam_indep A S)
    (Free.shift (A.corr S)) Free.one hp hl
  rw [Matrix.mul_one,Matrix.mul_one,←P4L.frame_eq_shift_blockMat] at h
  exact h.cast (fun φ => by simp [bcost,show S.card≠0 by omega])

theorem shift_walsh_square (A : OBase α) (p : α) (f : ℕ) (v : Sky α f → ℂ) (z : Sky α f) :
    P4L.walsh f (matAct f (Binary.shift (A.v p)) v) z =
      (P4L.prodF f (P4L.fr A {p}) z)^2 * P4L.walsh f v z := by
  have h : frame A {p} * frame A {p} = Binary.shift (A.v p) := by
    simpa only [FFTChainDFT.PhysicalNormalizer.single_frame_delta] using delta_sq (A.v p) (A.self p)
  rw [←h,←matAct_mul]
  simp only [P4L.walsh_frame,Pi.mul_apply]
  ring
end Main

section Geometry
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (base : T → OBase H) (l : H) (hH : Fintype.card H=9)

def stageD (f : ℕ) (g : Orth (LC (Fin 17) H l)) (t : T) (z : Sky (LC (Fin 17) H l) f) (s : Fin 18) : ℂ :=
  P4L.prodF f (P4L.fr (ChainG18.basisA base l g t) (ChainG18.incr l s.val)) z

def pivotQ (f : ℕ) (g : Orth (LC (Fin 17) H l)) (t : T) (z : Sky (LC (Fin 17) H l) f) : ℂ :=
  P4L.prodF f (P4L.fr (ChainG18.basisA base l g t) {Sum.inl l}) z

 def shift_step (a : Fin 40) : SimpleStep (Sl := Sl) (C := C) (stageD base l) (pivotQ base l) (.shift a) (fun _ => 0) := by
  let M := fun g t => Binary.shift ((ChainG18.basisA base l g t).v (Sum.inl l))
  refine ⟨mainWindow a M, (mainWindow_route a M (fun _ => 0) ?_).cast (fun _ _ => rfl) (fun _ => by simp), ?_, ?_⟩
  · intro g t ρ _ _ r
    exact P4L.gstep_shift r _
  · intro f y g t z
    apply State.ext_get
    intro i
    rw [viewAt_get,mainWindow_at]
    by_cases hi : i=a
    · subst i
      simp only [ite_true,Op.eval,State.get_set_same,viewAt_get]
      exact shift_walsh_square _ _ _ _ _
    · simp only [if_neg hi,Op.eval,State.get_set_ne _ _ _ _ hi,viewAt_get]
  · exact mainWindow_fresh a M

 def idle_step (a : Fin 40) (ks : List (Fin 18)) (hk : ks.Nodup) (h0 : 0<ks.length) (h8 : ks.length≤8) :
    SimpleStep (Sl := Sl) (C := C) (stageD base l) (pivotQ base l) (.idle a ks)
      (fun φ => (Fintype.card (Orth (LC (Fin 17) H l)) : ℝ)*(Fintype.card T : ℝ)*bcost φ (8*ks.length)) := by
  let S := FFTChainDFT.Chain.StageSets.selected l ks
  let M := fun g t => frame (ChainG18.basisA base l g t) S
  have hc : S.card=8*ks.length := FFTChainDFT.Chain.StageSets.selected_card l hH ks hk
  have hp : 1≤S.card := by rw [hc]; omega
  have hl : S.card<Fintype.card (LC (Fin 17) H l) := by
    rw [hc,ChainG18.card_LC145 l hH]; omega
  refine ⟨mainWindow a M, mainWindow_route a M (fun φ => bcost φ (8*ks.length)) ?_, ?_, ?_⟩
  · intro g t
    simpa only [hc] using greach_frame_set (ChainG18.basisA base l g t) S hp hl
  · intro f y g t z
    apply State.ext_get
    intro i
    rw [viewAt_get,mainWindow_at]
    by_cases hi : i=a
    · subst i
      simp only [ite_true,Op.eval,State.get_set_same,viewAt_get]
      rw [P4L.walsh_frame]
      change P4L.prodF f (P4L.fr (ChainG18.basisA base l g t) S) z * _ = _
      rw [FFTChainDFT.Chain.StageSets.selected_phase_at l f _ ks hk z]
      rfl
    · simp only [if_neg hi,Op.eval,State.get_set_ne _ _ _ _ hi,viewAt_get]
  · exact mainWindow_fresh a M
end Geometry
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.mainWindow_route
#print axioms OAI.PowerSaving.ChainNet.shift_step
#print axioms OAI.PowerSaving.ChainNet.idle_step
