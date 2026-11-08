from pathlib import Path
from fractions import Fraction as F
import json,sys,hashlib
root=Path(sys.argv[1]);events=json.loads((root/'certificates/paired-controller.json').read_text())['events']
raw=json.loads((root/'research/vendor/chain-CALLER.json').read_text())
# A row preserves insertion order exactly as Sparse.addTerm / Sparse.add.
rows=[[((0,(),r),F(1))] for r in range(40)]
def add(a,b):
 out=list(a)
 for m,c in b:
  if not c:continue
  for i,(n,v) in enumerate(out):
   if n==m:
    if v+c:out[i]=(n,v+c)
    else:out.pop(i)
    break
  else:out.append((m,c))
 return out
def scale(c,a):return [(m,c*v) for m,v in a]
def shift(p,ks,a):return [(((m[0]+p)%4,tuple(sorted(m[1]+tuple(ks))),m[2]),c) for m,c in a]
def step(e):
 k=e[0]
 if k=='ADD':rows[e[1]]=add(rows[e[1]],scale(F(e[3]),rows[e[2]]))
 elif k=='SCALE':rows[e[1]]=scale(F(e[2]),rows[e[1]])
 elif k=='SWAP':rows[e[1]],rows[e[2]]=rows[e[2]],rows[e[1]]
 elif k in ['H','HI']:
  a,b=e[1:];x,y=rows[a],rows[b];c=F(1,2) if k=='HI' else F(1)
  rows[a]=scale(c,add(x,y));rows[b]=scale(c,add(x,scale(F(-1),y)))
 elif k=='SHIFT_P':rows[e[1]]=shift(2,[],rows[e[1]])
 elif k=='QUERY':
  assert e[3]==-1
  rows[e[1]]=add(rows[e[1]],shift(3,[],rows[e[2]]))
 elif k=='LOCAL':
  _,i,a,b=e;x,y=rows[a],rows[b]
  rows[a]=shift(0,[i-1],x);rows[b]=shift(0,[i-1],add(y,shift(3,[],x)))
 elif k=='IDLE_ONE':rows[e[1]]=shift(0,[i-1 for i in e[2]],rows[e[1]])
 else:raise ValueError(k)
def op(e):
 k=e[0]
 if k=='ADD':return f'.add {e[1]} {e[2]} ({e[3]})'
 if k=='SCALE':return f'.scale {e[1]} ({e[2]})'
 if k=='SWAP':return f'.swap {e[1]} {e[2]}'
 if k=='SHIFT_P':return f'.shift {e[1]}'
 if k in ['H','HI']:return f'.'+('had' if k=='H' else 'hadInv')+f' {e[1]} {e[2]}'
 if k=='QUERY':return f'.query {e[1]} {e[2]}'
 if k=='LOCAL':return f'.full {e[1]-1} {e[2]} {e[3]}'
 if k=='IDLE_ONE':return f'.idle {e[1]} ['+', '.join(str(x-1) for x in e[2])+']'
 raise ValueError(k)
def rat(c):return str(c.numerator) if c.denominator==1 else f'({c.numerator}/{c.denominator})'
def row(a):return '['+', '.join('(('+str(m[0])+', ['+', '.join(map(str,m[1]))+'], '+str(m[2])+'), '+rat(c)+')' for m,c in a)+']'
def state(a):return '⟨\n'+',\n'.join(row(r) for r in a)+'\n⟩'
out=root/'Submission/Chain';out.mkdir(exist_ok=True)
chunk=40;names=[];total=0
for start in range(0,len(events),chunk):
 ns=f'Cert{start//chunk:02d}';names.append(ns);ins=state(rows)
 ev=events[start:start+chunk]
 for e in ev:step(e)
 s=f'''import Submission.Chain.EvalSparse
/-! Exact kernel certificate for paired controller events {start}..{start+len(ev)-1}.
Generated from the attributed literal schedule. No external computation is trusted. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace FFTChainDFT.Chain.{ns}
open Sparse
 def input : State Row := {ins}
 def output : State Row := {state(rows)}
 def code : List Op := ['''+',\n'.join(op(e) for e in ev)+''']
 theorem checked : Sparse.word code input = output := by decide +kernel
end FFTChainDFT.Chain.'''+ns+'\n#print axioms FFTChainDFT.Chain.'+ns+'.checked\n'
 (out/(ns+'.lean')).write_text(s);total+=len(s)
 print(ns,len(s),flush=True)
for r,a in enumerate(rows):
 d=raw['diagonal'][r%20];ks=tuple(i for i,n in enumerate(d[2:]) for _ in range(n))
 assert a==[((d[0]%4,ks,r),F(1))],(r,a)
s='\n'.join('import Submission.Chain.'+n for n in names)+'''
namespace FFTChainDFT.Chain
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
 theorem Sparse.word_append (a b : List Op) (s : State Sparse.Row) :
    Sparse.word (a++b) s = Sparse.word b (Sparse.word a s) := List.foldl_append
 def code : List Op := '''+' ++ '.join(n+'.code' for n in names)+'''
 theorem checked : Sparse.word code Cert00.input = Cert64.output := by
   simp only [code, Sparse.word_append]
   rw ['''+', '.join(n+'.checked' for n in names)+''']
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
'''
for r in range(39):s+='   | '+str(r)+' => ['+', '.join(map(str,rows[r][0][0][1]))+']\n'
s+='   | _ => ['+', '.join(map(str,rows[39][0][0][1]))+']\n'
s+=''' theorem endpoint (d : Fin 18 → R) (q : R) (hq : q^4=1) (u : State R) (r : Fin 40) :
   (evalWord d q code u).get r = q^3 * (stages r |>.map d).prod * u.get r := by
   rw [endpoint_state d q hq u]
   fin_cases r <;>
     simp [Sparse.stateVal, State.map, Cert64.output, Sparse.rowVal, Sparse.monVal, State.get, stages]
end
end FFTChainDFT.Chain
#print axioms FFTChainDFT.Chain.endpoint
'''
(out/'Controller.lean').write_text(s)
print('TOTAL',total+len(s))
