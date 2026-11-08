"""Audit actual Lean #print axioms output for all listed local theorems."""
from pathlib import Path
import re,subprocess,sys,json
ROOT=Path(__file__).resolve().parents[1]
p=subprocess.run(['lake','env','lean','Submission/LocalAudit.lean'],cwd=ROOT,text=True,capture_output=True)
sys.stdout.write(p.stdout);sys.stderr.write(p.stderr)
if p.returncode: raise SystemExit(p.returncode)
allowed={'propext','Classical.choice','Quot.sound'}
expected=re.findall(r'#print axioms ([A-Za-z0-9_.]+)',(ROOT/'Submission/LocalAudit.lean').read_text())
found={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",p.stdout):
    found[name]=set(a.strip() for a in axioms.split(',') if a.strip())
for name in re.findall(r"'([^']+)' does not depend on any axioms",p.stdout): found[name]=set()
if set(found)!=set(expected): raise SystemExit('Incomplete axiom output')
for name,axs in found.items():
    if axs-allowed: raise SystemExit('Unpermitted axioms for '+name+': '+str(axs-allowed))
receipt={'scope':'local theorems only; Race.bound absent','status':'passed',
         'theorems':{n:sorted(a) for n,a in sorted(found.items())}}
(ROOT/'certificates/local_axioms.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS_LOCAL_AXIOM_AUDIT',len(found),'theorems; this is not the final DFT theorem audit')
