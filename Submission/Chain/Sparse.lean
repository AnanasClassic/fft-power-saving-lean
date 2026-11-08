import Submission.Chain.Common
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! A sound exact sparse checker for the paired controller. The checker is
    executable; its semantic soundness is proved for arbitrary field data. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace FFTChainDFT.Chain
namespace Sparse
abbrev Mon := ℕ × List (Fin 18) × Fin 40
abbrev Row := List (Mon × ℚ)

def addTerm (m : Mon) (c : ℚ) (row : Row) : Row :=
  if c = 0 then row else
  match row with
  | [] => [(m,c)]
  | (n,b)::xs =>
    if n = m then
      if b+c = 0 then xs else (n,b+c)::xs
    else (n,b)::addTerm m c xs

def add (a : Row) : Row → Row
  | [] => a
  | (m,c)::xs => add (addTerm m c a) xs

def scale (c : ℚ) (a : Row) : Row := a.map fun (m,b) => (m,c*b)
def insertStage (a : Fin 18) : List (Fin 18) → List (Fin 18)
  | [] => [a]
  | b::xs => if a.val ≤ b.val then a::b::xs else b::insertStage a xs

def sortStages : List (Fin 18) → List (Fin 18)
  | [] => []
  | a::xs => insertStage a (sortStages xs)

lemma insertStage_perm (a : Fin 18) (xs : List (Fin 18)) : List.Perm (insertStage a xs) (a::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons b xs ih =>
    by_cases h : a.val ≤ b.val
    · simp [insertStage,h]
    · simp only [insertStage,h,ite_false]
      exact (ih.cons b).trans (List.Perm.swap a b xs)

lemma sortStages_perm (xs : List (Fin 18)) : List.Perm (sortStages xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a xs ih => exact (insertStage_perm a (sortStages xs)).trans (ih.cons a)

def shiftMon (p : ℕ) (ks : List (Fin 18)) (m : Mon) : Mon :=
  ((m.1+p)%4, sortStages (m.2.1++ks), m.2.2)
def shift (p : ℕ) (ks : List (Fin 18)) (a : Row) : Row :=
  a.map fun (m,c) => (shiftMon p ks m,c)

noncomputable section
variable {R : Type*} [Field R] [CharZero R]
def monVal (d : Fin 18 → R) (q : R) (u : State R) (m : Mon) : R :=
  q^m.1 * (m.2.1.map d).prod * u.get m.2.2
def rowVal (d : Fin 18 → R) (q : R) (u : State R) : Row → R
  | [] => 0
  | (m,c)::xs => (c:R)*monVal d q u m + rowVal d q u xs

lemma addTerm_val (d : Fin 18 → R) (q : R) (u : State R) (m : Mon) (c : ℚ) (a : Row) :
    rowVal d q u (addTerm m c a) = (c:R)*monVal d q u m + rowVal d q u a := by
  induction a with
  | nil => by_cases hc : c=0 <;> simp [addTerm, hc, rowVal]
  | cons a xs ih =>
    rcases a with ⟨n,b⟩
    by_cases hc : c=0
    · simp [addTerm,hc]
    by_cases hn : n=m
    · subst n
      by_cases hb : b+c=0
      · have he : (b:R)+(c:R)=0 := by exact_mod_cast hb
        simp only [addTerm,hc,if_false,if_pos,hb,rowVal]
        linear_combination -he * monVal d q u m
      · simp only [addTerm,hc,if_false,if_pos,hb,rowVal,Rat.cast_add]
        ring
    · simp only [addTerm,hc,if_false,hn,rowVal,ih]
      ring

lemma add_val (d : Fin 18 → R) (q : R) (u : State R) (a b : Row) :
    rowVal d q u (add a b) = rowVal d q u a + rowVal d q u b := by
  induction b generalizing a with
  | nil => simp [add,rowVal]
  | cons b xs ih =>
    rcases b with ⟨m,c⟩
    rw [add,ih,addTerm_val,rowVal]
    ring

lemma scale_val (d : Fin 18 → R) (q : R) (u : State R) (c : ℚ) (a : Row) :
    rowVal d q u (scale c a) = (c:R)*rowVal d q u a := by
  induction a with
  | nil => simp [scale,rowVal]
  | cons a xs ih =>
    rcases a with ⟨m,b⟩
    simp only [scale,List.map_cons,rowVal,Rat.cast_mul] at *
    rw [ih]; ring

lemma pow_mod (q : R) (hq : q^4=1) (n : ℕ) : q^(n%4)=q^n := by
  have hn := Nat.mod_add_div n 4
  calc
    q^(n%4) = q^(n%4) * (q^4)^(n/4) := by rw [hq,one_pow,mul_one]
    _ = q^(n%4+4*(n/4)) := by rw [pow_add,pow_mul]
    _ = q^n := congrArg (q^·) hn

lemma shiftMon_val (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R)
    (p : ℕ) (ks : List (Fin 18)) (m : Mon) :
    monVal d q u (shiftMon p ks m) = q^p * (ks.map d).prod * monVal d q u m := by
  have hs := (sortStages_perm (m.2.1++ks)).map d
  have hv := hs.prod_eq
  simp only [monVal,shiftMon,pow_mod q hq,List.map_append,List.prod_append] at *
  rw [hv,pow_add]
  ring

lemma shift_val (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R)
    (p : ℕ) (ks : List (Fin 18)) (a : Row) :
    rowVal d q u (shift p ks a) = q^p*(ks.map d).prod*rowVal d q u a := by
  induction a with
  | nil => simp [shift,rowVal]
  | cons a xs ih =>
    rcases a with ⟨m,c⟩
    simp only [shift,List.map_cons,rowVal,shiftMon_val d q hq] at *
    rw [ih]; ring
end
end Sparse
end FFTChainDFT.Chain
