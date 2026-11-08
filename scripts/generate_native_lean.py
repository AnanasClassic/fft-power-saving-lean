"""Lower the reconstructed schedule to the pinned, sound KLW certificate interface.

Upstream P104W data and theorems are preserved. Only event segments 3/4,
one intermediate row trie, and the paid-rank list change. All generated
certificate equalities must be proved by Lean; Python is not trusted.
"""
from pathlib import Path
from fractions import Fraction as F
import re,json,gzip,hashlib,sys
PROJECT=Path(sys.argv[1])
DATA=PROJECT/'Submission/Work/FwdOnly/Gen/P104W'
BASE=PROJECT/'research/vendor/owned772-WORD.json.gz'
NEW=PROJECT/'certificates/modified-native.json.gz'

def need(ok,msg):
 if not ok:raise ValueError(msg)

def split_list(s):
 out=[];start=depth=0
 for i,c in enumerate(s):
  if c in '([':depth+=1
  elif c in ')]':depth-=1
  elif c==',' and depth==0:out.append(s[start:i].strip());start=i+1
 if s[start:].strip():out.append(s[start:].strip())
 return out
s='\n'.join((DATA/f'D{i}.lean').read_text() for i in range(4))
blocks={m[1]:split_list(m[2]) for m in re.finditer(r'noncomputable def (ev\d+_\d+) : List \(KLW.WEv\) := \[(.*?)\]\n',s)}
segments=[[e for name,es in blocks.items() if name.startswith(f'ev{n}_') for e in es] for n in range(7)]
base=json.loads(gzip.decompress(BASE.read_bytes()));candidate=json.loads(gzip.decompress(NEW.read_bytes()))
rmap={};fmap={};cmap={}
for m in re.finditer(r'noncomputable def k(\d+) : GXD.Co := ⟨(true|false), (\d+), (\d+)⟩',s):cmap[F((-1 if m[2]=='true' else 1)*int(m[3]),int(m[4]))]=int(m[1])
for i,(a,b) in enumerate(zip(base['program'],sum(segments,[]))):
 op=a[0]
 if op in ['ADD','COPY']:
  m=re.fullmatch(r'\.g \(\.out (\d+) (\d+) \[\((\d+), k(\d+)\)\] \[\]\)',b);need(m is not None,f'ADD encoding {i}')
  ff,src,dst,co=map(int,m.groups());rmap[a[1]]=dst;rmap[a[2]]=src;fmap[a[-1]]=ff;need(co==cmap[F(a[-2])],'coefficient')
 elif op=='SCALE':
  m=re.fullmatch(r'\.sc (\d+) (\d+) k(\d+)',b);need(m is not None,'scale')
  ff,rr,co=map(int,m.groups());rmap[a[1]]=rr;fmap[a[-1]]=ff;need(co==cmap[F(a[-2])],'scale coefficient')
 elif op=='INIT':
  m=re.fullmatch(r'\.za (\d+) (\d+)',b);need(m is not None,'INIT');rr,ff=map(int,m.groups());rmap[a[1]]=rr;fmap[a[-1]]=ff
 elif op=='CLEAR':
  m=re.fullmatch(r'\.zf (\d+)',b);need(m is not None,'CLEAR');rmap[a[1]]=int(m[1])
 elif op=='MOVE':
  m=re.fullmatch(r'\.dn (\d+) (\d+)',b) if a[-1] else re.fullmatch(r'\.g \(\.out (\d+) (\d+) \[\] \[\]\)',b)
  need(m is not None,'MOVE')
  if a[-1]:rr,ff=map(int,m.groups())
  else:ff,rr=map(int,m.groups())
  rmap[a[1]]=rr;fmap[a[3]]=ff

def encode(e):
 op=e[0];r=rmap[e[1]]
 if op in ['ADD','COPY']:return f'.g (.out {fmap[e[4]]} {rmap[e[2]]} [({r}, k{cmap[F(e[3])]})] [])'
 if op=='SCALE':return f'.sc {fmap[e[3]]} {r} k{cmap[F(e[2])]}'
 if op=='INIT':return f'.za {r} {fmap[e[2]]}'
 if op=='CLEAR':return f'.zf {r}'
 if op=='MOVE':return f'.dn {r} {fmap[e[3]]}' if e[4] else f'.g (.out {fmap[e[3]]} {r} [] [])'
 raise ValueError(op)
need([encode(e) for e in base['program']]==sum(segments,[]),'exact baseline lowering')
cuts=[0]
for x in segments:cuts.append(cuts[-1]+len(x))
newcuts=[0]
newpr=candidate['program']
for cut in cuts[1:-1]:
 needle=base['program'][cut:cut+12]
 matches=[i for i,e in enumerate(newpr) if e==needle[0] and newpr[i:i+12]==needle]
 need(len(matches)==1,'unambiguous cut anchor');newcuts.append(matches[0])
newcuts.append(len(newpr))
newsegments=[[encode(e) for e in newpr[newcuts[i]:newcuts[i+1]]] for i in range(7)]
need([i for i in range(7) if newsegments[i]!=segments[i]]==[3,4],'only two segments change')

def snapshot(word,cut):
 rows=[{i:F(1)} for i in range(799)]
 for e in word['program'][:cut]:
  op=e[0];r=e[1]
  if op in ['INIT','CLEAR']:rows[r]={}
  elif op=='SCALE':rows[r]={k:v*F(e[2]) for k,v in rows[r].items()}
  elif op in ['ADD','COPY']:
   d={} if op=='COPY' else dict(rows[r])
   for k,v in rows[e[2]].items():
    d[k]=d.get(k,F(0))+F(e[3])*v
    if not d[k]:del d[k]
   rows[r]=d
 return [{rmap[k]:int(v*16) for k,v in row.items() if v} for row in rows]
# Check exact divisibility independently, before emitting Int coefficients.
def int_snapshot(word,cut):
 rows=[{i:F(1)} for i in range(799)]
 for e in word['program'][:cut]:
  op=e[0];r=e[1]
  if op in ['INIT','CLEAR']:rows[r]={}
  elif op=='SCALE':rows[r]={k:v*F(e[2]) for k,v in rows[r].items()}
  elif op in ['ADD','COPY']:
   d={} if op=='COPY' else dict(rows[r])
   for k,v in rows[e[2]].items():
    d[k]=d.get(k,F(0))+F(e[3])*v
    if not d[k]:del d[k]
   rows[r]=d
 out={}
 for r,row in enumerate(rows):
  need(all((v*16).denominator==1 for v in row.values()),'coefficient denominator 16')
  out[rmap[r]]={rmap[k]:int(v*16) for k,v in row.items()}
 return out
old=int_snapshot(base,cuts[4]);new=int_snapshot(candidate,newcuts[4])
diff={r:new[r] for r in new if new[r]!=old[r]}
need(int_snapshot(base,cuts[5])==int_snapshot(candidate,newcuts[5]),'rows rejoin at segment-4 endpoint')
print('cuts',cuts,newcuts,'changed midpoint rows',sorted(diff),flush=True)

header='''import Submission.Work.FwdOnly.Gen.P104W

/-!
Reconstructed owned772 supplier with the two attributed local edits.
This file contains data only. Every semantic certificate is checked in Lean.
DreamingOfClouds: helper732 schedule; Ali Romman: retained operand for reader451.
P104W and its original certificate: CubeJerry and predecessor authors, Jacob
Sussman and Halit Ziya Kartal. See research/sources.md and retained notices.
Generated by scripts/generate_native_lean.py.
-/
set_option maxRecDepth 100000
namespace FFTChainDFT.Native
open GXD.P104W
'''
lines=[header]
def listdef(name,ty,values):
 names=[]
 for k in range(0,len(values),150):
  sub=f'{name}_{k//150}';names.append(sub)
  lines.append(f'noncomputable def {sub} : List {ty} := ['+', '.join(values[k:k+150])+']\n')
 lines.append(f'noncomputable def {name} : List {ty} := '+' ++ ('.join(names)+')'*(len(names)-1)+'\n')
for n in [3,4]:listdef(f'ev{n}mod','KLW.WEv',newsegments[n])
lines.append('noncomputable def evsMod : List KLW.WEv := ev0 ++ (ev1 ++ (ev2 ++ (ev3mod ++ (ev4mod ++ (ev5 ++ ev6)))))\n')
def litint(n):return str(n) if n>=0 else f'(Int.negSucc {-n-1})'
expr='GXD.P104W.rfM4'
for r,row in sorted(diff.items()):expr=f'({expr}.set {r} ['+', '.join(f'({k}, {litint(v)})' for k,v in sorted(row.items()))+'])'
lines.append('noncomputable def rfMidMod : KLW.RT := '+expr+'\n')
ranks=[str(abs(len(candidate['frames'][e[2]])-len(candidate['frames'][e[3]]))) for e in newpr if e[0]=='MOVE']
listdef('ranksMod','Nat',ranks)
lines.append('end FFTChainDFT.Native\n')
out=PROJECT/'Submission/Native';out.mkdir(parents=True,exist_ok=True)
(out/'ModifiedData.lean').write_text('\n'.join(lines))
receipt={'baseline_cuts':cuts,'modified_cuts':newcuts,'changed_midpoint_registers':sorted(diff),'events':len(newpr),'paid_calls':len(ranks),'source_sha256':hashlib.sha256(gzip.decompress(NEW.read_bytes())).hexdigest()}
(PROJECT/'certificates/native_lowering.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Emitted ModifiedData.lean',sum(map(len,lines)),'bytes')
