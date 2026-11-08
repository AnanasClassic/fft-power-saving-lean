import Submission.Chain.Physical.Word
import Submission.Native.HelperHistogram
import Submission.InventoryLink
/-! Exact live-role counts, adapted from Kartal's BQ19.CertGen.card_live.
The forty main roles and all 36 fresh supplier banks remain independent. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR BC GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
lemma card_live {Γ T Sl : Type} [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T] [Fintype Sl]
    [DecidableEq Sl] (f : PLive Γ T Sl → ℕ) (fm : Fin 40 → ℕ) (ff : Sl → ℕ)
    (hm : ∀ g i t, f (Sum.inl (g, (i, t))) = fm i) (hf : ∀ g k q, f (Sum.inr (g, (k, q))) = ff q) (r : ℕ) :
    (Finset.univ.filter fun l => f l = r).card
      = Fintype.card Γ * ∑ i, Fintype.card T * (if fm i = r then 1 else 0)
        + Fintype.card Γ * (36 * ∑ q, if ff q = r then 1 else 0) := by
  rw [Finset.card_filter, Fintype.sum_sum_type]
  have h1 : ∀ g : Γ, (∑ y : Fin 40 × T, if f (Sum.inl (g, y)) = r then 1 else 0)
      = ∑ i, Fintype.card T * (if fm i = r then 1 else 0) := by
    intro g
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : ∀ t : T, (if f (Sum.inl (g, (i, t))) = r then 1 else 0) = (if fm i = r then 1 else 0) :=
      fun t => by rw [hm g i t]
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h2 : ∀ g : Γ, (∑ y : Fin 36 × Sl, if f (Sum.inr (g, y)) = r then 1 else 0)
      = 36 * ∑ q, if ff q = r then 1 else 0 := by
    intro g
    rw [Fintype.sum_prod_type]
    have e : ∀ (k : Fin 36) (q : Sl),
        (if f (Sum.inr (g, (k, q))) = r then 1 else 0) = (if ff q = r then 1 else 0) :=
      fun k q => by rw [hf g k q]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => e k q)), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h1' : (∑ x : Γ × (Fin 40 × T), if f (Sum.inl x) = r then 1 else 0)
      = Fintype.card Γ * ∑ i, Fintype.card T * (if fm i = r then 1 else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have h2' : (∑ x : Γ × (Fin 36 × Sl), if f (Sum.inr x) = r then 1 else 0)
      = Fintype.card Γ * (36 * ∑ q, if ff q = r then 1 else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun g _ => h2 g), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  rw [h1', h2']


theorem count_eq_sum {A : Type} [DecidableEq A] (r : A) (xs : List A) :
    xs.count r = (xs.map fun x => if x=r then (1:ℕ) else 0).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a=r
    · subst a; simp only [List.count_cons_self,List.map_cons,List.sum_cons,ite_true,ih]; omega
    · simp only [List.count_cons_of_ne ha,List.map_cons,List.sum_cons,if_neg ha,zero_add,ih]

theorem mainMultiplicity_sum (r : ℕ) :
    Schedule.mainMultiplicity r = ∑ i : Fin 40, if 1+8*(Schedule.targetStages i).length=r then 1 else 0 := by
  rw [Schedule.mainMultiplicity,count_eq_sum,List.map_ofFn,Fin.sum_ofFn]
  rfl

theorem main_rank_bounds : ∀ i : Fin 40,
    1≤1+8*(Schedule.targetStages i).length ∧ 1+8*(Schedule.targetStages i).length≤145 := by decide +kernel
end
end OAI.PowerSaving.ChainNet
