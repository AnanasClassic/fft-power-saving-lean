"""Adapt the pinned all-length Fourier transfer to the new certified kernel.
No old final bound or old finite instance is imported. Original notices remain.
"""
from pathlib import Path
import hashlib,json,re,sys
up=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
lineage={}
number_facts='''namespace SeamChain18
lemma alphaChain18_lt_alpha : alphaChain18 < alpha := by norm_num [alphaChain18,alpha]
lemma alphaChain18_theta : alphaChain18 < theta := alphaChain18_lt_alpha.trans Skies.alpha_theta
lemma alphaChain18_decimal : alphaChain18 < decimalExponent ∧ decimalExponent < 1 := by
  norm_num [decimalExponent,alphaChain18]
def targetExponentChain18 : ℝ := 1-statedSavingChain18
def fallbackExponentChain18 : ℝ := 1-102210/(10:ℝ)^8
lemma alphaChain18_lt_target : alphaChain18 < targetExponentChain18 := by
  norm_num [alphaChain18,targetExponentChain18,statedSavingChain18]
lemma alphaChain18_lt_fallback : alphaChain18 < fallbackExponentChain18 := by
  norm_num [alphaChain18,fallbackExponentChain18]
lemma target_lt_fallbackChain18 : targetExponentChain18 < fallbackExponentChain18 := by
  norm_num [targetExponentChain18,fallbackExponentChain18,statedSavingChain18]
lemma target_posChain18 : 0<targetExponentChain18 := by
  norm_num [targetExponentChain18,statedSavingChain18]
lemma target_lt_oneChain18 : targetExponentChain18<1 := by
  norm_num [targetExponentChain18,statedSavingChain18]
lemma fallback_lt_oneChain18 : fallbackExponentChain18<1 := by norm_num [fallbackExponentChain18]
lemma target_lt_decimalChain18 : targetExponentChain18<decimalExponent := by
  norm_num [targetExponentChain18,decimalExponent,statedSavingChain18]
lemma fallback_lt_decimalChain18 : fallbackExponentChain18<decimalExponent := by
  norm_num [fallbackExponentChain18,decimalExponent]
lemma target_lt_thetaChain18 : targetExponentChain18<theta :=
  (show targetExponentChain18<alpha by norm_num [targetExponentChain18,alpha,statedSavingChain18]).trans Skies.alpha_theta
lemma fallback_lt_thetaChain18 : fallbackExponentChain18<theta :=
  (show fallbackExponentChain18<alpha by norm_num [fallbackExponentChain18,alpha]).trans Skies.alpha_theta
end SeamChain18'''
for name in ['Goal','Merged1','WorkingTransform','Merged2','Main']:
 p=up/(name+'.lean');raw=p.read_text();s=raw
 s=s.replace('Submission.Work.BQT.FourierTB','Submission.Chain.Fourier').replace('TB19','Chain18')
 s=re.sub(r'3148496240\s*/\s*\(10\s*:\s*ℝ\)\s*\^\s*12','6727247/(2000000000:ℝ)',s)
 if name=='Goal':
  s=s.replace('def statedSavingChain18 : ℝ := Real.pi / 1000','def statedSavingChain18 : ℝ := 3363623/1000000000')
 if name=='Merged1':
  s=s.replace('import Submission.Work.BQT.TB.Stmt','import Submission.Chain.EngineBound')
  s=s.replace('import Submission.Work.BQT.TB.Engine\n','')
  s=s.replace('MX.Chain18.EngineStmt.lift MX.Chain18.engine cl m k v','FFTChainDFT.engine cl m k v')
  start=s.index('namespace SeamChain18',s.index('## 5. Number facts'))
  end=s.index('end SeamChain18',start)+len('end SeamChain18')
  s=s[:start]+number_facts+s[end:]
 pre='''/-!
Adapted for the paired 18-stage witness from the pinned Kartal FourierTB
transfer at verifier commit195060b222d63c2a22cf8f5dd390f34e9b446323.
The all-length Fourier reduction and computational model are inherited from
OpenAI; Sussman supplies the engine/seam integration and Kartal the prior
instantiation. This adaptation uses FFTChainDFT.engine, seam saving
0.0033636235 and final exact saving3363623/1000000000. Original source
comments below describe their historical construction and retain attribution.
-/
'''
 (out/(name+'.lean')).write_text(pre+s)
 lineage[name]={'upstream_commit':'195060b222d63c2a22cf8f5dd390f34e9b446323','upstream_path':'submissions/dft/halitziyakartal-halitziyav6-pi/Submission/Work/BQT/FourierTB/'+name+'.lean','upstream_sha256':hashlib.sha256(raw.encode()).hexdigest(),'adapted_path':'Submission/Chain/Fourier/'+name+'.lean','changes':['namespace suffixChain18','new kernel seam','exact rational engine/final exponents']}
(out/'lineage.json').write_text(json.dumps(lineage,indent=2)+'\n')
