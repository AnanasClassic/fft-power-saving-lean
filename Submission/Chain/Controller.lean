import Submission.Chain.Cert00
import Submission.Chain.Cert01
import Submission.Chain.Cert02
import Submission.Chain.Cert03
import Submission.Chain.Cert04
import Submission.Chain.Cert05
import Submission.Chain.Cert06
import Submission.Chain.Cert07
import Submission.Chain.Cert08
import Submission.Chain.Cert09
import Submission.Chain.Cert10
import Submission.Chain.Cert11
import Submission.Chain.Cert12
import Submission.Chain.Cert13
import Submission.Chain.Cert14
import Submission.Chain.Cert15
import Submission.Chain.Cert16
import Submission.Chain.Cert17
import Submission.Chain.Cert18
import Submission.Chain.Cert19
import Submission.Chain.Cert20
import Submission.Chain.Cert21
import Submission.Chain.Cert22
import Submission.Chain.Cert23
import Submission.Chain.Cert24
import Submission.Chain.Cert25
import Submission.Chain.Cert26
import Submission.Chain.Cert27
import Submission.Chain.Cert28
import Submission.Chain.Cert29
import Submission.Chain.Cert30
import Submission.Chain.Cert31
import Submission.Chain.Cert32
import Submission.Chain.Cert33
import Submission.Chain.Cert34
import Submission.Chain.Cert35
import Submission.Chain.Cert36
import Submission.Chain.Cert37
import Submission.Chain.Cert38
import Submission.Chain.Cert39
import Submission.Chain.Cert40
import Submission.Chain.Cert41
import Submission.Chain.Cert42
import Submission.Chain.Cert43
import Submission.Chain.Cert44
import Submission.Chain.Cert45
import Submission.Chain.Cert46
import Submission.Chain.Cert47
import Submission.Chain.Cert48
import Submission.Chain.Cert49
import Submission.Chain.Cert50
import Submission.Chain.Cert51
import Submission.Chain.Cert52
import Submission.Chain.Cert53
import Submission.Chain.Cert54
import Submission.Chain.Cert55
import Submission.Chain.Cert56
import Submission.Chain.Cert57
import Submission.Chain.Cert58
import Submission.Chain.Cert59
import Submission.Chain.Cert60
import Submission.Chain.Cert61
import Submission.Chain.Cert62
import Submission.Chain.Cert63
import Submission.Chain.Cert64
namespace FFTChainDFT.Chain
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
 theorem Sparse.word_append (a b : List Op) (s : State Sparse.Row) :
    Sparse.word (a++b) s = Sparse.word b (Sparse.word a s) := List.foldl_append
 def code : List Op := Cert00.code ++ Cert01.code ++ Cert02.code ++ Cert03.code ++ Cert04.code ++ Cert05.code ++ Cert06.code ++ Cert07.code ++ Cert08.code ++ Cert09.code ++ Cert10.code ++ Cert11.code ++ Cert12.code ++ Cert13.code ++ Cert14.code ++ Cert15.code ++ Cert16.code ++ Cert17.code ++ Cert18.code ++ Cert19.code ++ Cert20.code ++ Cert21.code ++ Cert22.code ++ Cert23.code ++ Cert24.code ++ Cert25.code ++ Cert26.code ++ Cert27.code ++ Cert28.code ++ Cert29.code ++ Cert30.code ++ Cert31.code ++ Cert32.code ++ Cert33.code ++ Cert34.code ++ Cert35.code ++ Cert36.code ++ Cert37.code ++ Cert38.code ++ Cert39.code ++ Cert40.code ++ Cert41.code ++ Cert42.code ++ Cert43.code ++ Cert44.code ++ Cert45.code ++ Cert46.code ++ Cert47.code ++ Cert48.code ++ Cert49.code ++ Cert50.code ++ Cert51.code ++ Cert52.code ++ Cert53.code ++ Cert54.code ++ Cert55.code ++ Cert56.code ++ Cert57.code ++ Cert58.code ++ Cert59.code ++ Cert60.code ++ Cert61.code ++ Cert62.code ++ Cert63.code ++ Cert64.code
 theorem checked : Sparse.word code Cert00.input = Cert64.output := by
   simp only [code, Sparse.word_append]
   rw [Cert00.checked, Cert01.checked, Cert02.checked, Cert03.checked, Cert04.checked, Cert05.checked, Cert06.checked, Cert07.checked, Cert08.checked, Cert09.checked, Cert10.checked, Cert11.checked, Cert12.checked, Cert13.checked, Cert14.checked, Cert15.checked, Cert16.checked, Cert17.checked, Cert18.checked, Cert19.checked, Cert20.checked, Cert21.checked, Cert22.checked, Cert23.checked, Cert24.checked, Cert25.checked, Cert26.checked, Cert27.checked, Cert28.checked, Cert29.checked, Cert30.checked, Cert31.checked, Cert32.checked, Cert33.checked, Cert34.checked, Cert35.checked, Cert36.checked, Cert37.checked, Cert38.checked, Cert39.checked, Cert40.checked, Cert41.checked, Cert42.checked, Cert43.checked, Cert44.checked, Cert45.checked, Cert46.checked, Cert47.checked, Cert48.checked, Cert49.checked, Cert50.checked, Cert51.checked, Cert52.checked, Cert53.checked, Cert54.checked, Cert55.checked, Cert56.checked, Cert57.checked, Cert58.checked, Cert59.checked, Cert60.checked, Cert61.checked, Cert62.checked, Cert63.checked, Cert64.checked]
noncomputable section
variable {R : Type*} [Field R] [CharZero R]
 theorem input_val (d : Fin 18 → R) (q : R) (u : State R) :
   Sparse.stateVal d q u Cert00.input = u := by
   simp [Sparse.stateVal, State.map, Cert00.input, Sparse.rowVal, Sparse.monVal, State.get]
 theorem endpoint_state (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R) :
   evalWord d q code u = Sparse.stateVal d q u Cert64.output := by
   rw [←input_val d q u]
   exact Sparse.certificate d q hq u code Cert00.input Cert64.output checked
 def stages (r : Fin 40) : List (Fin 18) :=
   match r.val with
   | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
   | 1 => [0, 1, 2, 3, 4, 5, 6, 7, 8]
   | 2 => [1, 2, 3, 4, 5, 6, 7, 8]
   | 3 => [2, 3, 4, 5, 6, 7, 8]
   | 4 => [3, 4, 5, 6, 7, 8]
   | 5 => [4, 5, 6, 7, 8]
   | 6 => [5, 6, 7, 8]
   | 7 => [6, 7, 8]
   | 8 => [7, 8]
   | 9 => [8]
   | 10 => [9]
   | 11 => [9, 10]
   | 12 => [9, 10, 11]
   | 13 => [9, 10, 11, 12]
   | 14 => [9, 10, 11, 12, 13]
   | 15 => [9, 10, 11, 12, 13, 14]
   | 16 => [9, 10, 11, 12, 13, 14, 15]
   | 17 => [9, 10, 11, 12, 13, 14, 15, 16]
   | 18 => [9, 10, 11, 12, 13, 14, 15, 16, 17]
   | 19 => []
   | 20 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
   | 21 => [0, 1, 2, 3, 4, 5, 6, 7, 8]
   | 22 => [1, 2, 3, 4, 5, 6, 7, 8]
   | 23 => [2, 3, 4, 5, 6, 7, 8]
   | 24 => [3, 4, 5, 6, 7, 8]
   | 25 => [4, 5, 6, 7, 8]
   | 26 => [5, 6, 7, 8]
   | 27 => [6, 7, 8]
   | 28 => [7, 8]
   | 29 => [8]
   | 30 => [9]
   | 31 => [9, 10]
   | 32 => [9, 10, 11]
   | 33 => [9, 10, 11, 12]
   | 34 => [9, 10, 11, 12, 13]
   | 35 => [9, 10, 11, 12, 13, 14]
   | 36 => [9, 10, 11, 12, 13, 14, 15]
   | 37 => [9, 10, 11, 12, 13, 14, 15, 16]
   | 38 => [9, 10, 11, 12, 13, 14, 15, 16, 17]
   | _ => []
 theorem endpoint (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R) (r : Fin 40) :
   (evalWord d q code u).get r = q^3 * (stages r |>.map d).prod * u.get r := by
   rw [endpoint_state d q hq u]
   fin_cases r <;>
     simp [Sparse.stateVal, State.map, Cert64.output, Sparse.rowVal, Sparse.monVal, State.get, stages]
end
end FFTChainDFT.Chain
#print axioms FFTChainDFT.Chain.endpoint
