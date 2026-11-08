import Submission.Chain.Geometry.Lemmas
namespace FFTChainDFT.Chain.StageSets
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.BC OAI.PowerSaving.ChainG18
noncomputable section
variable {H : Type} [Fintype H] [DecidableEq H]
abbrev Labels (l : H) := LC (Fin 17) H l

def selected (l : H) : List (Fin 18) → Finset (Labels l)
  | [] => ∅
  | k::ks => incr l k.val ∪ selected l ks

theorem increments_disjoint (l : H) (a b : Fin 18) (hne : a≠b) :
    Disjoint (incr l a.val) (incr l b.val) := by
  have hn : a.val≠b.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hn with hab|hab
  · exact disj_incr l _ b.val b.isLt (incr_sub_setX l a.val b.val hab (by omega))
  · exact (disj_incr l _ a.val a.isLt (incr_sub_setX l b.val a.val hab (by omega))).symm

theorem mem_selected (l : H) (ks : List (Fin 18)) (x : Labels l) :
    x ∈ selected l ks ↔ ∃ k ∈ ks, x ∈ incr l k.val := by
  induction ks with
  | nil => simp [selected]
  | cons a ks ih =>
    simp only [selected,Finset.mem_union,ih,List.mem_cons]
    constructor
    · rintro (h|⟨b,hb,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨b,Or.inr hb,h⟩
    · rintro ⟨b,(rfl|hb),h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,hb,h⟩

theorem disjoint_selected (l : H) (a : Fin 18) (ks : List (Fin 18)) (ha : a∉ks) :
    Disjoint (incr l a.val) (selected l ks) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨b,hb,hxb⟩ := (mem_selected l ks x).mp hy
  have hn : a≠b := by rintro rfl; exact ha hb
  exact (Finset.disjoint_left.mp (increments_disjoint l a b hn)) hx hxb

theorem selected_card (l : H) (hH : Fintype.card H=9) (ks : List (Fin 18)) (h : ks.Nodup) :
    (selected l ks).card=8*ks.length := by
  revert h
  induction ks with
  | nil => intro h; simp [selected]
  | cons a ks ih =>
    intro h
    obtain ⟨ha,hks⟩ := List.nodup_cons.mp h
    rw [selected,Finset.card_union_of_disjoint (disjoint_selected l a ks ha),
      card_incr l hH a.val a.isLt,ih hks]
    simp only [List.length_cons]
    omega

theorem selected_pivot_disjoint (l : H) (ks : List (Fin 18)) :
    Disjoint (selected l ks) {Sum.inl l} := by
  apply Finset.disjoint_left.mpr
  intro x hx hp
  obtain ⟨k,hk,hxk⟩ := (mem_selected l ks x).mp hx
  have hd := disj_incr l ({Sum.inl l} : Finset (Labels l)) k.val k.isLt
    (pivot_sub_setX l k.val (by omega))
  exact (Finset.disjoint_left.mp hd) hp hxk

def targetSet (l : H) (ks : List (Fin 18)) : Finset (Labels l) := selected l ks ∪ {Sum.inl l}
theorem target_card (l : H) (hH : Fintype.card H=9) (ks : List (Fin 18)) (h : ks.Nodup) :
    (targetSet l ks).card=1+8*ks.length := by
  rw [targetSet,Finset.card_union_of_disjoint (selected_pivot_disjoint l ks),
    selected_card l hH ks h,Finset.card_singleton]
  omega

theorem fr_empty (l : H) (A : OBase (Labels l)) : P4L.fr A ∅=1 := by
  funext x
  simp [P4L.fr,OBase.proj]

theorem selected_phase (l : H) (A : OBase (Labels l)) (ks : List (Fin 18)) (h : ks.Nodup) :
    P4L.fr A (selected l ks) = (ks.map (fun k => P4L.fr A (incr l k.val))).prod := by
  revert h
  induction ks with
  | nil => intro h; simpa [selected] using fr_empty l A
  | cons a ks ih =>
    intro h
    obtain ⟨ha,hks⟩ := List.nodup_cons.mp h
    rw [selected,P4L.fr_union A _ _ (disjoint_selected l a ks ha),ih hks]
    rfl

theorem prodF_mul_at (l : H) (f : ℕ) (φ ψ : Space (Labels l) → ℂ) (z : Sky (Labels l) f) :
    P4L.prodF f (φ*ψ) z = P4L.prodF f φ z * P4L.prodF f ψ z :=
  congrFun (P4L.prodF_mul f φ ψ) z

theorem selected_phase_at (l : H) (f : ℕ) (A : OBase (Labels l)) (ks : List (Fin 18)) (h : ks.Nodup)
    (z : Sky (Labels l) f) :
    P4L.prodF f (P4L.fr A (selected l ks)) z =
      (ks.map (fun k => P4L.prodF f (P4L.fr A (incr l k.val)) z)).prod := by
  revert h
  induction ks with
  | nil =>
    intro h
    simp only [selected,fr_empty,List.map_nil,List.prod_nil]
    exact congrFun (P4L.prodF_one (α := Labels l) f) z
  | cons a ks ih =>
    intro h
    obtain ⟨ha,hks⟩ := List.nodup_cons.mp h
    rw [selected,P4L.fr_union A _ _ (disjoint_selected l a ks ha),prodF_mul_at]
    rw [ih hks]
    rfl

theorem target_phase_at (l : H) (f : ℕ) (A : OBase (Labels l)) (ks : List (Fin 18)) (h : ks.Nodup)
    (z : Sky (Labels l) f) :
    P4L.prodF f (P4L.fr A (targetSet l ks)) z = P4L.prodF f (P4L.fr A {Sum.inl l}) z *
      (ks.map (fun k => P4L.prodF f (P4L.fr A (incr l k.val)) z)).prod := by
  rw [targetSet,P4L.fr_union A _ _ (selected_pivot_disjoint l ks),prodF_mul_at]
  rw [selected_phase_at l f A ks h z]
  exact mul_comm _ _
end
end FFTChainDFT.Chain.StageSets
#print axioms FFTChainDFT.Chain.StageSets.target_card
#print axioms FFTChainDFT.Chain.StageSets.target_phase_at
