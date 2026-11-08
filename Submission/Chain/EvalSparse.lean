import Submission.Chain.Sparse
import Submission.Chain.StateMap
namespace FFTChainDFT.Chain.Sparse
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def run (op : Op) (u : State Row) : State Row :=
  match op with
  | .add a b c => u.set a (add (u.get a) (scale c (u.get b)))
  | .scale a c => u.set a (scale c (u.get a))
  | .swap a b => (u.set a (u.get b)).set b (u.get a)
  | .shift a => u.set a (shift 2 [] (u.get a))
  | .had a b => (u.set a (add (u.get a) (u.get b))).set b (add (u.get a) (scale (-1) (u.get b)))
  | .hadInv a b => (u.set a (scale (1/2) (add (u.get a) (u.get b)))).set b
      (scale (1/2) (add (u.get a) (scale (-1) (u.get b))))
  | .query a b => u.set a (add (u.get a) (shift 3 [] (u.get b)))
  | .full k a b => (u.set a (shift 0 [k] (u.get a))).set b
      (shift 0 [k] (add (u.get b) (shift 3 [] (u.get a))))
  | .idle a ks => u.set a (shift 0 ks (u.get a))

def word (ops : List Op) (s : State Row) : State Row := ops.foldl (fun v op => run op v) s

noncomputable section
variable {R : Type*} [Field R] [CharZero R]
def stateVal (d : Fin 18 → R) (q : R) (u : State R) (s : State Row) : State R :=
  s.map (rowVal d q u)

theorem run_correct (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R)
    (op : Op) (s : State Row) :
    stateVal d q u (run op s) = Op.eval d q op (stateVal d q u s) := by
  cases op <;>
    simp only [run,Op.eval,stateVal,State.map_set,State.map_get,
      add_val,scale_val,shift_val d q hq,List.map_nil,List.prod_nil,
      List.map_cons,List.prod_cons,pow_zero,one_mul,mul_one,
      Rat.cast_neg,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,div_eq_mul_inv,Rat.cast_inv,sub_eq_add_neg,
      neg_mul,one_div,mul_comm]

 theorem word_correct (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R)
    (ops : List Op) (s : State Row) :
    stateVal d q u (word ops s) = evalWord d q ops (stateVal d q u s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons a ops ih =>
    change stateVal d q u (word ops (run a s)) =
      evalWord d q ops (Op.eval d q a (stateVal d q u s))
    rw [ih,run_correct d q hq]

 theorem certificate (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R)
    (ops : List Op) (s t : State Row) (h : word ops s = t) :
    evalWord d q ops (stateVal d q u s) = stateVal d q u t := by
  rw [←word_correct d q hq u ops s,h]
end
end FFTChainDFT.Chain.Sparse
#print axioms FFTChainDFT.Chain.Sparse.certificate
