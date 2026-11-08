import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Fin.Basic

/-!
Pure scalar semantics of the rational paired 9+9 controller.
The literal schedule is DreamingOfClouds' PR6833, paired using the rational
normalizer. The certificate method follows Kartal's stepwise controller replay.
No physical operator contract is asserted by this scalar layer alone.
-/
set_option maxRecDepth 100000
namespace FFTChainDFT.Chain

@[ext] structure State (R : Type*) where
  r00 : R
  r01 : R
  r02 : R
  r03 : R
  r04 : R
  r05 : R
  r06 : R
  r07 : R
  r08 : R
  r09 : R
  r10 : R
  r11 : R
  r12 : R
  r13 : R
  r14 : R
  r15 : R
  r16 : R
  r17 : R
  r18 : R
  r19 : R
  r20 : R
  r21 : R
  r22 : R
  r23 : R
  r24 : R
  r25 : R
  r26 : R
  r27 : R
  r28 : R
  r29 : R
  r30 : R
  r31 : R
  r32 : R
  r33 : R
  r34 : R
  r35 : R
  r36 : R
  r37 : R
  r38 : R
  r39 : R
  deriving DecidableEq

namespace State
variable {R : Type*}
def get (u : State R) (i : Fin 40) : R :=
  match i.val with
  | 0 => u.r00
  | 1 => u.r01
  | 2 => u.r02
  | 3 => u.r03
  | 4 => u.r04
  | 5 => u.r05
  | 6 => u.r06
  | 7 => u.r07
  | 8 => u.r08
  | 9 => u.r09
  | 10 => u.r10
  | 11 => u.r11
  | 12 => u.r12
  | 13 => u.r13
  | 14 => u.r14
  | 15 => u.r15
  | 16 => u.r16
  | 17 => u.r17
  | 18 => u.r18
  | 19 => u.r19
  | 20 => u.r20
  | 21 => u.r21
  | 22 => u.r22
  | 23 => u.r23
  | 24 => u.r24
  | 25 => u.r25
  | 26 => u.r26
  | 27 => u.r27
  | 28 => u.r28
  | 29 => u.r29
  | 30 => u.r30
  | 31 => u.r31
  | 32 => u.r32
  | 33 => u.r33
  | 34 => u.r34
  | 35 => u.r35
  | 36 => u.r36
  | 37 => u.r37
  | 38 => u.r38
  | _ => u.r39
def set (u : State R) (i : Fin 40) (x : R) : State R :=
  match i.val with
  | 0 => {u with r00 := x}
  | 1 => {u with r01 := x}
  | 2 => {u with r02 := x}
  | 3 => {u with r03 := x}
  | 4 => {u with r04 := x}
  | 5 => {u with r05 := x}
  | 6 => {u with r06 := x}
  | 7 => {u with r07 := x}
  | 8 => {u with r08 := x}
  | 9 => {u with r09 := x}
  | 10 => {u with r10 := x}
  | 11 => {u with r11 := x}
  | 12 => {u with r12 := x}
  | 13 => {u with r13 := x}
  | 14 => {u with r14 := x}
  | 15 => {u with r15 := x}
  | 16 => {u with r16 := x}
  | 17 => {u with r17 := x}
  | 18 => {u with r18 := x}
  | 19 => {u with r19 := x}
  | 20 => {u with r20 := x}
  | 21 => {u with r21 := x}
  | 22 => {u with r22 := x}
  | 23 => {u with r23 := x}
  | 24 => {u with r24 := x}
  | 25 => {u with r25 := x}
  | 26 => {u with r26 := x}
  | 27 => {u with r27 := x}
  | 28 => {u with r28 := x}
  | 29 => {u with r29 := x}
  | 30 => {u with r30 := x}
  | 31 => {u with r31 := x}
  | 32 => {u with r32 := x}
  | 33 => {u with r33 := x}
  | 34 => {u with r34 := x}
  | 35 => {u with r35 := x}
  | 36 => {u with r36 := x}
  | 37 => {u with r37 := x}
  | 38 => {u with r38 := x}
  | _ => {u with r39 := x}
end State

inductive Op where
  | add (dst src : Fin 40) (c : ℚ)
  | scale (r : Fin 40) (c : ℚ)
  | swap (a b : Fin 40)
  | shift (r : Fin 40)
  | had (a b : Fin 40)
  | hadInv (a b : Fin 40)
  | query (dst src : Fin 40)
  | full (k : Fin 18) (src dst : Fin 40)
  | idle (r : Fin 40) (stages : List (Fin 18))
  deriving Repr

noncomputable section
variable {R : Type*} [Field R] [CharZero R]

def Op.eval (d : Fin 18 → R) (q : R) (op : Op) (u : State R) : State R :=
  match op with
  | .add a b c => u.set a (u.get a + (c : R)*u.get b)
  | .scale a c => u.set a ((c : R)*u.get a)
  | .swap a b => (u.set a (u.get b)).set b (u.get a)
  | .shift a => u.set a (q^2 * u.get a)
  | .had a b => (u.set a (u.get a + u.get b)).set b (u.get a - u.get b)
  | .hadInv a b => (u.set a ((u.get a + u.get b)/2)).set b ((u.get a - u.get b)/2)
  | .query a b => u.set a (u.get a + q^3*u.get b)
  | .full k a b => (u.set a (d k*u.get a)).set b (d k*(u.get b + q^3*u.get a))
  | .idle a ks => u.set a ((ks.map d).prod*u.get a)

def evalWord (d : Fin 18 → R) (q : R) (ops : List Op) (u : State R) : State R :=
  ops.foldl (fun v op => op.eval d q v) u

lemma pow5 (q : R) (hq : q^4=1) : q^5=q := by rw [pow_succ, hq, one_mul]
lemma pow6 (q : R) (hq : q^4=1) : q^6=q^2 := by
  rw [show (6:ℕ)=4+2 by decide, pow_add, hq, one_mul]

end
end FFTChainDFT.Chain
