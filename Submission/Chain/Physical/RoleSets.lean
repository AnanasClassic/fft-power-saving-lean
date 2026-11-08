import Submission.Chain.Physical.Roles
/-! Role sets for the 40-array / 36-bank network. Adapted from Kartal's
P4L.Seg and BQ19 word adapters; every bank retains all of its native slots. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset
noncomputable section
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ]
  [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

def freshAll : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × Fin 36 × Sl)).image fun p => freshR p.1 p.2.1 p.2.2

def mainAll : Finset (PRole Γ T Sl C) :=
  (Finset.univ : Finset (Γ × Fin 40 × T)).image fun p => mainR p.1 p.2.1 p.2.2

theorem fresh_mem_freshAll (g : Γ) (k : Fin 36) (q : Sl) :
    freshR (T := T) (C := C) g k q ∈ freshAll :=
  Finset.mem_image.mpr ⟨(g,k,q),Finset.mem_univ _,rfl⟩

theorem main_mem_mainAll (g : Γ) (i : Fin 40) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∈ mainAll :=
  Finset.mem_image.mpr ⟨(g,i,t),Finset.mem_univ _,rfl⟩

theorem main_not_freshAll (g : Γ) (i : Fin 40) (t : T) :
    mainR (Sl := Sl) (C := C) g i t ∉ freshAll := by
  rintro h
  obtain ⟨⟨g',k,q⟩,_,e⟩ := Finset.mem_image.mp h
  cases e

theorem fresh_not_mainAll (g : Γ) (k : Fin 36) (q : Sl) :
    freshR (T := T) (C := C) g k q ∉ mainAll := by
  rintro h
  obtain ⟨⟨g',i,t⟩,_,e⟩ := Finset.mem_image.mp h
  cases e

theorem of_mem_freshAll {r : PRole Γ T Sl C} (h : r ∈ freshAll) :
    ∃ g k q, r=freshR g k q := by
  obtain ⟨⟨g,k,q⟩,_,e⟩ := Finset.mem_image.mp h
  exact ⟨g,k,q,e.symm⟩

def freshMat (Z : Fin 36 → Γ → Sl → CMat α) : PRole Γ T Sl C → CMat α
  | .inl (.inr (g,(k,q))) => Z k g q
  | _ => 1

def freshTgt (D : Sl → Finset α) : PRole Γ T Sl C → CMat α
  | .inl (.inr (_,(_,q))) => GF.pk (D q)
  | _ => 1
end
end OAI.PowerSaving.ChainNet
