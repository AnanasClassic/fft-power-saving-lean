import Submission.Chain.Controller
/-! The universal induction used by the physical compiler. It does not
postulate physical realizability: each instruction must supply the stated
all-data commutation theorem before this result can be instantiated. -/
namespace FFTChainDFT.Chain
set_option maxRecDepth 100000
noncomputable section
variable {D R : Type*} [Field R] [CharZero R]

def interpret (step : Op → D → D) (ops : List Op) (v : D) : D :=
  ops.foldl (fun v op => step op v) v

 theorem interpret_view (d : Fin 18 → R) (q : R) (read : D → State R)
    (step : Op → D → D) (ops : List Op)
    (hstep : ∀ op ∈ ops, ∀ v, read (step op v) = Op.eval d q op (read v)) (v : D) :
    read (interpret step ops v) = evalWord d q ops (read v) := by
  induction ops generalizing v with
  | nil => rfl
  | cons a ops ih =>
    change read (interpret step ops (step a v)) =
      evalWord d q ops (Op.eval d q a (read v))
    rw [ih (fun op hop w => hstep op (List.mem_cons_of_mem a hop) w)]
    rw [hstep a (List.mem_cons_self) v]

/-- Once the physical primitive lemmas are supplied, the literal controller
endpoint follows for every input, without further circuit simulation. -/
 theorem interpret_endpoint (d : Fin 18 → R) (q : R) (hq : q^4=1)
    (read : D → State R) (step : Op → D → D)
    (hstep : ∀ op ∈ code, ∀ v, read (step op v) = Op.eval d q op (read v)) (v : D) (r : Fin 40) :
    (read (interpret step code v)).get r = q^3 * (stages r |>.map d).prod * (read v).get r := by
  rw [interpret_view d q read step code hstep v]
  exact endpoint d q hq (read v) r
end
end FFTChainDFT.Chain
#print axioms FFTChainDFT.Chain.interpret_endpoint
