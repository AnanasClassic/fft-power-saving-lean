import Submission.Chain.Schedule
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
 theorem code_eq_schedule : code = Schedule.code := rfl
theorem link00 : Cert00.output = Cert01.input := rfl
theorem link01 : Cert01.output = Cert02.input := rfl
theorem link02 : Cert02.output = Cert03.input := rfl
theorem link03 : Cert03.output = Cert04.input := rfl
theorem link04 : Cert04.output = Cert05.input := rfl
theorem link05 : Cert05.output = Cert06.input := rfl
theorem link06 : Cert06.output = Cert07.input := rfl
theorem link07 : Cert07.output = Cert08.input := rfl
theorem link08 : Cert08.output = Cert09.input := rfl
theorem link09 : Cert09.output = Cert10.input := rfl
theorem link10 : Cert10.output = Cert11.input := rfl
theorem link11 : Cert11.output = Cert12.input := rfl
theorem link12 : Cert12.output = Cert13.input := rfl
theorem link13 : Cert13.output = Cert14.input := rfl
theorem link14 : Cert14.output = Cert15.input := rfl
theorem link15 : Cert15.output = Cert16.input := rfl
theorem link16 : Cert16.output = Cert17.input := rfl
theorem link17 : Cert17.output = Cert18.input := rfl
theorem link18 : Cert18.output = Cert19.input := rfl
theorem link19 : Cert19.output = Cert20.input := rfl
theorem link20 : Cert20.output = Cert21.input := rfl
theorem link21 : Cert21.output = Cert22.input := rfl
theorem link22 : Cert22.output = Cert23.input := rfl
theorem link23 : Cert23.output = Cert24.input := rfl
theorem link24 : Cert24.output = Cert25.input := rfl
theorem link25 : Cert25.output = Cert26.input := rfl
theorem link26 : Cert26.output = Cert27.input := rfl
theorem link27 : Cert27.output = Cert28.input := rfl
theorem link28 : Cert28.output = Cert29.input := rfl
theorem link29 : Cert29.output = Cert30.input := rfl
theorem link30 : Cert30.output = Cert31.input := rfl
theorem link31 : Cert31.output = Cert32.input := rfl
theorem link32 : Cert32.output = Cert33.input := rfl
theorem link33 : Cert33.output = Cert34.input := rfl
theorem link34 : Cert34.output = Cert35.input := rfl
theorem link35 : Cert35.output = Cert36.input := rfl
theorem link36 : Cert36.output = Cert37.input := rfl
theorem link37 : Cert37.output = Cert38.input := rfl
theorem link38 : Cert38.output = Cert39.input := rfl
theorem link39 : Cert39.output = Cert40.input := rfl
theorem link40 : Cert40.output = Cert41.input := rfl
theorem link41 : Cert41.output = Cert42.input := rfl
theorem link42 : Cert42.output = Cert43.input := rfl
theorem link43 : Cert43.output = Cert44.input := rfl
theorem link44 : Cert44.output = Cert45.input := rfl
theorem link45 : Cert45.output = Cert46.input := rfl
theorem link46 : Cert46.output = Cert47.input := rfl
theorem link47 : Cert47.output = Cert48.input := rfl
theorem link48 : Cert48.output = Cert49.input := rfl
theorem link49 : Cert49.output = Cert50.input := rfl
theorem link50 : Cert50.output = Cert51.input := rfl
theorem link51 : Cert51.output = Cert52.input := rfl
theorem link52 : Cert52.output = Cert53.input := rfl
theorem link53 : Cert53.output = Cert54.input := rfl
theorem link54 : Cert54.output = Cert55.input := rfl
theorem link55 : Cert55.output = Cert56.input := rfl
theorem link56 : Cert56.output = Cert57.input := rfl
theorem link57 : Cert57.output = Cert58.input := rfl
theorem link58 : Cert58.output = Cert59.input := rfl
theorem link59 : Cert59.output = Cert60.input := rfl
theorem link60 : Cert60.output = Cert61.input := rfl
theorem link61 : Cert61.output = Cert62.input := rfl
theorem link62 : Cert62.output = Cert63.input := rfl
theorem link63 : Cert63.output = Cert64.input := rfl
 theorem checked : Sparse.word code Cert00.input = Cert64.output := by
   simp only [code, Sparse.word_append]
   rw [Cert00.checked, link00, Cert01.checked, link01, Cert02.checked, link02, Cert03.checked, link03, Cert04.checked, link04, Cert05.checked, link05, Cert06.checked, link06, Cert07.checked, link07, Cert08.checked, link08, Cert09.checked, link09, Cert10.checked, link10, Cert11.checked, link11, Cert12.checked, link12, Cert13.checked, link13, Cert14.checked, link14, Cert15.checked, link15, Cert16.checked, link16, Cert17.checked, link17, Cert18.checked, link18, Cert19.checked, link19, Cert20.checked, link20, Cert21.checked, link21, Cert22.checked, link22, Cert23.checked, link23, Cert24.checked, link24, Cert25.checked, link25, Cert26.checked, link26, Cert27.checked, link27, Cert28.checked, link28, Cert29.checked, link29, Cert30.checked, link30, Cert31.checked, link31, Cert32.checked, link32, Cert33.checked, link33, Cert34.checked, link34, Cert35.checked, link35, Cert36.checked, link36, Cert37.checked, link37, Cert38.checked, link38, Cert39.checked, link39, Cert40.checked, link40, Cert41.checked, link41, Cert42.checked, link42, Cert43.checked, link43, Cert44.checked, link44, Cert45.checked, link45, Cert46.checked, link46, Cert47.checked, link47, Cert48.checked, link48, Cert49.checked, link49, Cert50.checked, link50, Cert51.checked, link51, Cert52.checked, link52, Cert53.checked, link53, Cert54.checked, link54, Cert55.checked, link55, Cert56.checked, link56, Cert57.checked, link57, Cert58.checked, link58, Cert59.checked, link59, Cert60.checked, link60, Cert61.checked, link61, Cert62.checked, link62, Cert63.checked, link63, Cert64.checked]
noncomputable section
variable {R : Type*} [Field R] [CharZero R]
 theorem input_val (d : Fin 18 → R) (q : R) (u : State R) :
   Sparse.stateVal d q u Cert00.input = u := by
   simp [Sparse.stateVal, State.map, Cert00.input, Sparse.rowVal, Sparse.monVal, State.get]
 theorem endpoint_state (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R) :
   evalWord d q code u = Sparse.stateVal d q u Cert64.output := by
   conv_lhs => rw [←input_val d q u]
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
