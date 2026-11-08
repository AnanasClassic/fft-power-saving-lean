import Submission.Chain.Physical.Gates
import Submission.Chain.GateAlgebra
/-! Physical rational gates, including their effect on arbitrary dirty helpers.
Hadamard and swap layers are finite compositions of elementary rational letters.
Every realization is a proper trusted GWord at all widths, of zero paid price. -/
namespace OAI.PowerSaving.ChainNet
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW FFTChainDFT.Chain
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
variable {α Γ T Sl C : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ]
  [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (d : ∀ f : ℕ, Γ → T → Sky α f → Fin 18 → ℂ)
  (q : ∀ f : ℕ, Γ → T → Sky α f → ℂ)

/-- A realizable instruction which leaves every productive helper unchanged. -/
structure SimpleStep (op : Op) (price : (ℕ → ℝ) → ℝ) where
  run : ∀ f : ℕ, Data α (PRole Γ T Sl C) f → Data α (PRole Γ T Sl C) f
  route : P4L.ORoute run price
  main : ∀ f y g t z, viewAt f g t z (run f y) = Op.eval (d f g t z) (q f g t z) op (viewAt f g t z y)
  fresh : ∀ f y g k s, run f y (freshR g k s) = y (freshR g k s)

 def add_step (a b : Fin 40) (c : ℚ) : SimpleStep (Sl := Sl) (C := C) d q (.add a b c) (fun _ => 0) where
  run := fun f y => point f (actPoint (linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) (GateAlgebra.addMat a b c))) y
  route := gate_route _
  main := by
    intro f y g t z
    apply State.ext_get
    intro i
    rw [viewAt_gate]
    exact GateAlgebra.add_eval (d f g t z) (q f g t z) (viewAt f g t z y) a b i c
  fresh := by
    intro f y g k s
    apply linMat_other
    intro g' i' t' h
    cases h

 def scale_step (a : Fin 40) (c : ℚ) : SimpleStep (Sl := Sl) (C := C) d q (.scale a c) (fun _ => 0) where
  run := fun f y => point f (actPoint (linMat (Γ := Γ) (T := T) (Sl := Sl) (C := C) (GateAlgebra.scaleMat a c))) y
  route := gate_route _
  main := by
    intro f y g t z
    apply State.ext_get
    intro i
    rw [viewAt_gate]
    exact GateAlgebra.scale_eval (d f g t z) (q f g t z) (viewAt f g t z y) a i c
  fresh := by
    intro f y g k s
    apply linMat_other
    intro g' i' t' h
    cases h

 def had_step (a b : Fin 40) (h : a≠b) : SimpleStep (Sl := Sl) (C := C) d q (.had a b) (fun _ => 0) := by
  let sa := add_step (Sl := Sl) (C := C) d q a b 1
  let sb := scale_step (Sl := Sl) (C := C) d q b (-2)
  let sc := add_step (Sl := Sl) (C := C) d q b a 1
  refine ⟨fun f y => sc.run f (sb.run f (sa.run f y)),
    ((sa.route.trans sb.route).trans sc.route).cast (fun _ _ => rfl) (fun _ => by simp), ?_, ?_⟩
  · intro f y g t z
    rw [sc.main,sb.main,sa.main]
    exact GateAlgebra.had_as_gates (d f g t z) (q f g t z) a b h _
  · intro f y g k s
    rw [sc.fresh,sb.fresh,sa.fresh]

 def hadInv_step (a b : Fin 40) (h : a≠b) : SimpleStep (Sl := Sl) (C := C) d q (.hadInv a b) (fun _ => 0) := by
  let sa := had_step (Sl := Sl) (C := C) d q a b h
  let sb := scale_step (Sl := Sl) (C := C) d q a (1/2)
  let sc := scale_step (Sl := Sl) (C := C) d q b (1/2)
  refine ⟨fun f y => sc.run f (sb.run f (sa.run f y)),
    ((sa.route.trans sb.route).trans sc.route).cast (fun _ _ => rfl) (fun _ => by simp), ?_, ?_⟩
  · intro f y g t z
    rw [sc.main,sb.main,sa.main]
    exact GateAlgebra.hadInv_as_gates (d f g t z) (q f g t z) a b h _
  · intro f y g k s
    rw [sc.fresh,sb.fresh,sa.fresh]

 def swap_step (a b : Fin 40) (h : a≠b) : SimpleStep (Sl := Sl) (C := C) d q (.swap a b) (fun _ => 0) := by
  let sa := add_step (Sl := Sl) (C := C) d q a b 1
  let sb := scale_step (Sl := Sl) (C := C) d q b (-1)
  let sc := add_step (Sl := Sl) (C := C) d q b a 1
  let sd := add_step (Sl := Sl) (C := C) d q a b (-1)
  refine ⟨fun f y => sd.run f (sc.run f (sb.run f (sa.run f y))),
    (((sa.route.trans sb.route).trans sc.route).trans sd.route).cast (fun _ _ => rfl) (fun _ => by simp), ?_, ?_⟩
  · intro f y g t z
    rw [sd.main,sc.main,sb.main,sa.main]
    exact GateAlgebra.swap_as_gates (d f g t z) (q f g t z) a b h _
  · intro f y g k s
    rw [sd.fresh,sc.fresh,sb.fresh,sa.fresh]
end
end OAI.PowerSaving.ChainNet
#print axioms OAI.PowerSaving.ChainNet.had_step
#print axioms OAI.PowerSaving.ChainNet.swap_step
