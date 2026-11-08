import Submission.Work.Reframe.SNet
import Submission.Work.P4L.ORoute
import Submission.Chain.Common
-- Adapted from Kartal BQ19.Roles: 40 main roles, 36 native calls, six queries.
-- The embedding and lift proofs are inherited unchanged apart from types.

/-!
# Physical roles for the rational paired 9+9 controller

Adapted from Kartal's BQ19.Roles and Sussman's route lift. Live roles are
40 main arrays per port and fresh helper banks for each of 36 native calls.
Scratch consists of the supplier's owned copies and six query registers
per port. Copy-zero LOCAL calls use (1,0), copy-one calls use (21,20).
All inherited authorship remains with the upstream contributors.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace ChainNet
open Binary Matrix Finset RF

noncomputable section

/-- the live roles: main `(g, i, t)` and fresh helpers `(g, k, q)`. -/
abbrev PLive (Γ T Sl : Type) := (Γ × ((Fin 40) × T)) ⊕ (Γ × (Fin 36 × Sl))

/-- the scratch roles: the provider's copies and the thin-query scratch. -/
abbrev PScr (Γ T C : Type) := (Γ × C) ⊕ (Γ × (Fin 6 × T))

/-- all roles. -/
abbrev PRole (Γ T Sl C : Type) := PLive Γ T Sl ⊕ PScr Γ T C

/-- explicit decidable equality (the nested sum is beyond the default instance-search size). -/
instance instDecEqPLive {Γ T Sl : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] :
    DecidableEq (PLive Γ T Sl) := inferInstanceAs (DecidableEq ((Γ × ((Fin 40) × T)) ⊕ (Γ × (Fin 36 × Sl))))
instance instDecEqPScr {Γ T C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq C] :
    DecidableEq (PScr Γ T C) := inferInstanceAs (DecidableEq ((Γ × C) ⊕ (Γ × (Fin 6 × T))))
instance instDecEqPRole {Γ T Sl C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] [DecidableEq C] :
    DecidableEq (PRole Γ T Sl C) := @instDecidableEqSum (PLive Γ T Sl) (PScr Γ T C) instDecEqPLive instDecEqPScr

section Roles
variable {Γ T Sl C : Type}

def mainR (g : Γ) (i : (Fin 40)) (t : T) : PRole Γ T Sl C := Sum.inl (Sum.inl (g, (i, t)))
def freshR (g : Γ) (k : Fin 36) (q : Sl) : PRole Γ T Sl C := Sum.inl (Sum.inr (g, (k, q)))
def copyR (g : Γ) (c : C) : PRole Γ T Sl C := Sum.inr (Sum.inl (g, c))
def zR (g : Γ) (j : Fin 6) (t : T) : PRole Γ T Sl C := Sum.inr (Sum.inr (g, (j, t)))

/-- LOCAL copy zero uses roles (1,0), copy one uses (21,20). -/
def xOf (k : Fin 36) : Fin 40 := if k.val % 2 = 0 then 1 else 21
def yOf (k : Fin 36) : Fin 40 := if k.val % 2 = 0 then 0 else 20
lemma xOf_ne_yOf (k : Fin 36) : xOf k ≠ yOf k := by
  by_cases h : k.val % 2 = 0 <;> simp [xOf,yOf,h]

/-- the roles of the provider's stage, placed on the network at full call `k`. -/
def embF (k : Fin 36) : SRole Γ T Sl C → PRole Γ T Sl C
  | .inl (.inl (.inl (g, t))) => mainR g (xOf k) t
  | .inl (.inl (.inr (g, t))) => mainR g (yOf k) t
  | .inl (.inr (g, q)) => freshR g k q
  | .inr (g, c) => copyR g c

lemma embF_inj (k : Fin 36) : Function.Injective (embF (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) := by
  intro a b h
  have hxy := xOf_ne_yOf k
  rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩) <;>
    rcases b with (((⟨g', t'⟩ | ⟨g', t'⟩) | ⟨g', q'⟩) | ⟨g', c'⟩) <;>
    simp_all [embF, mainR, freshR, copyR]

def emb (k : Fin 36) : SRole Γ T Sl C ↪ PRole Γ T Sl C := ⟨embF k, embF_inj k⟩

@[simp] lemma emb_X (k : Fin 36) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jX (g, t)) = mainR g (xOf k) t := rfl
@[simp] lemma emb_Y (k : Fin 36) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jY (g, t)) = mainR g (yOf k) t := rfl
@[simp] lemma emb_S (k : Fin 36) (g : Γ) (q : Sl) :
    emb (T := T) (C := C) k (jS (g, q)) = freshR g k q := rfl
@[simp] lemma emb_C (k : Fin 36) (g : Γ) (c : C) :
    emb (T := T) (Sl := Sl) k (jC (g, c)) = copyR g c := rfl

variable [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C]

/-- the roles the full call `k` covers: the acting pair, the helpers of call `k`, the copies. -/
lemma covered_emb (k : Fin 36) (r : PRole Γ T Sl C) :
    r ∈ covered (emb (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) ↔
      (∃ g t, r = mainR g (xOf k) t) ∨ (∃ g t, r = mainR g (yOf k) t) ∨ (∃ g q, r = freshR g k q) ∨
        (∃ g c, r = copyR g c) := by
  rw [cover_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · exact Or.inl ⟨g, t, rfl⟩
    · exact Or.inr (Or.inl ⟨g, t, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨g, q, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨g, c, rfl⟩))
  · rintro (⟨g, t, rfl⟩ | ⟨g, t, rfl⟩ | ⟨g, q, rfl⟩ | ⟨g, c, rfl⟩)
    · exact ⟨jX (g, t), rfl⟩
    · exact ⟨jY (g, t), rfl⟩
    · exact ⟨jS (g, q), rfl⟩
    · exact ⟨jC (g, c), rfl⟩

end Roles

end
end ChainNet
end PowerSaving
end OAI

