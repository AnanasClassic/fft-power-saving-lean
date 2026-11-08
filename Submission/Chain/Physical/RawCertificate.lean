import Submission.Chain.Physical.Word
import Submission.Chain.Physical.Cost
import Submission.Chain.Physical.Count
import Submission.Work.Mixed.Bridge.Core
/-! The concrete raw finite witness for the modified supplier and paired 9+9
controller. Uses the certificate shape of Kartal's RawBQT772 and Sussman's
mixed tensor engine. All supplier/helper and main ranks are the new inventory. -/
namespace FFTChainDFT.Finite
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.ChainNet
open OAI.PowerSaving.RF OAI.PowerSaving.BC OAI.PowerSaving.GX OAI.PowerSaving.GF
open Matrix Finset
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def l0 : Fin 9 := 0
abbrev Labels := LC (Fin 17) (Fin 9) l0
abbrev Gauges := Orth Labels

theorem window_ok (n : ℕ) (g : Gauges) : Native.okW (ChainG18.winN l0 (Fintype.card_fin 9) n g) := by
  unfold ChainG18.winN
  split <;> exact Native.okC_generic _ _ _ _ _

def D9 : Finset Labels := ChainG18.setX l0 1

theorem card_D9 : D9.card=9 := by
  rw [D9,ChainG18.card_setX l0 (Fintype.card_fin 9) 1 (by norm_num)]

theorem res_le (q : Fin 562) : Fintype.card (Fin 9)-(Native.provider.ent q).dim ≤ D9.card := by
  rw [card_D9,Fintype.card_fin]
  omega

def Dr (q : Fin 562) : Finset Labels := Classical.choose (Finset.exists_subset_card_eq (res_le q))

theorem Dr_card (q : Fin 562) : (Dr q).card=Fintype.card (Fin 9)-(Native.provider.ent q).dim :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (res_le q))).2

theorem rank_main (base : Fin 104 → OBase (Fin 9)) (g : Gauges) (i : Fin 40) (t : Fin 104) :
    (rawTz base l0 Dr (Sum.inl (g,(i,t)))).1=1+8*(Chain.Schedule.targetStages i).length :=
  Chain.StageSets.target_card l0 (Fintype.card_fin 9) _ (Chain.Schedule.target_stages_nodup i)

theorem rank_raw (base : Fin 104 → OBase (Fin 9)) (p : PLive Gauges (Fin 104) (Fin 562)) :
    1≤(rawTz base l0 Dr p).1 ∧ (rawTz base l0 Dr p).1≤145 := by
  rcases p with ⟨g,i,t⟩|⟨g,k,q⟩
  · rw [rank_main]
    exact main_rank_bounds i
  · change 1≤(Dr q).card ∧ (Dr q).card≤145
    rw [Dr_card]
    have h := Native.helper_rank_bounds q
    omega

theorem target_count (base : Fin 104 → OBase (Fin 9)) (r : ℕ) :
    (Finset.univ.filter fun p : PLive Gauges (Fin 104) (Fin 562) => (rawTz base l0 Dr p).1=r).card =
      Fintype.card Gauges * Inventory.targetCount r := by
  rw [card_live (fun p => (rawTz base l0 Dr p).1)
    (fun i => 1+8*(Chain.Schedule.targetStages i).length) (fun q => (Dr q).card)
    (fun g i t => rank_main base g i t) (fun _ _ _ => rfl) r,←Nat.mul_add]
  refine congrArg (fun n : ℕ => Fintype.card Gauges*n) ?_
  simp only [Fintype.card_fin,Dr_card]
  rw [←Finset.mul_sum,←mainMultiplicity_sum,Native.helper_histogram]
  rw [←Chain.Schedule.productive_from_endpoints r]
  exact Nat.add_comm _ _

/-- A price identity for every price list determines the actual word histogram. -/
theorem hist_of_price {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (w : GWord α ρ) (G : ℕ) (P : List (ℕ × ℕ))
    (h : ∀ φ, w.costR φ=(G:ℝ)*listCost φ P) (r : ℕ) :
    w.hist r=G*BlockAccounting.histFn P r := by
  have hi := PB.hist_eq_price h r
  have hl : listCost (PB.ind r) P = (BlockAccounting.histFn P r : ℝ) := listCost_ind P r
  rw [hl] at hi
  exact_mod_cast hi

/-- Concrete finite word with the all-array live contract and both complete
histograms. No asymptotic theorem is imported to establish this witness. -/
theorem rawCert_exists : ∃ (α ρ σ : Type) (_ : Fintype α) (_ : DecidableEq α)
    (_ : Fintype ρ) (_ : DecidableEq ρ) (_ : Fintype σ) (_ : DecidableEq σ),
    ∃ (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ p, Fin (tr p) → Space α) (w : GWord α ρ) (G : ℕ),
      Function.Injective e ∧ (∀ p, LinearIndependent F (tz p)) ∧ w.Proper (Fintype.card α) ∧
      MX.GLiveKernelM e (fun p => blockMat (tz p)) w ∧
      1≤G ∧ Fintype.card α=145 ∧ (∀ p,1≤tr p ∧ tr p≤145) ∧
      (∀ r, (Finset.univ.filter fun p => tr p=r).card=G*BlockAccounting.histFn Analytic.targetHist r) ∧
      (∀ r, w.hist r=G*BlockAccounting.histFn Analytic.paidHist r) := by
  obtain ⟨base,hbase⟩ := Native.base_exists l0
  obtain ⟨w,hw,hc,hkernel⟩ := wordCert Native.provider base l0 hbase (Fintype.card_fin 9) window_ok Dr Dr_card
  have hcost : ∀ φ, w.costR φ=(Fintype.card Gauges:ℝ)*listCost φ Analytic.paidHist := by
    intro φ
    rw [hc φ,native_schedule_price]
  have hcnt (r : ℕ) :
      (Finset.univ.filter fun p : PLive Gauges (Fin 104) (Fin 562) => (rawTz base l0 Dr p).1=r).card =
        Fintype.card Gauges * BlockAccounting.histFn Analytic.targetHist r := by
    change _=Fintype.card Gauges*Analytic.histCount Analytic.targetHist r
    rw [Analytic.target_histogram_link]
    exact target_count base r
  refine ⟨Labels,PRole Gauges (Fin 104) (Fin 562) (Fin 29),PLive Gauges (Fin 104) (Fin 562),
    inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  exact ⟨Sum.inl,fun p => (rawTz base l0 Dr p).1,fun p => (rawTz base l0 Dr p).2,w,
    Fintype.card Gauges,Sum.inl_injective,rawTz_indep base l0 Dr,hw,hkernel,Orth.card_pos,
    ChainG18.card_LC145 l0 (Fintype.card_fin 9),rank_raw base,hcnt,hist_of_price w _ _ hcost⟩

end
end FFTChainDFT.Finite
#print axioms FFTChainDFT.Finite.rawCert_exists
