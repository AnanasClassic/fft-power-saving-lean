"""Audit actual Lean #print axioms output for all listed local theorems."""
from pathlib import Path
import re,subprocess,sys,json,argparse
ROOT=Path(__file__).resolve().parents[1]
args=argparse.ArgumentParser()
args.add_argument('--file',default='Submission/LocalAudit.lean')
args.add_argument('--receipt',default='certificates/local_axioms.json')
args.add_argument('--scope',default='local theorems only; Race.bound absent')
options=args.parse_args()
p=subprocess.run(['lake','env','lean',options.file],cwd=ROOT,text=True,capture_output=True)
sys.stdout.write(p.stdout);sys.stderr.write(p.stderr)
if p.returncode: raise SystemExit(p.returncode)
allowed={'propext','Classical.choice','Quot.sound'}
expected=re.findall(r'#print axioms ([A-Za-z0-9_.]+)',(ROOT/options.file).read_text())
found={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",p.stdout):
    found[name]=set(a.strip() for a in axioms.split(',') if a.strip())
for name in re.findall(r"'([^']+)' does not depend on any axioms",p.stdout): found[name]=set()
if set(found)!=set(expected): raise SystemExit('Incomplete axiom output')
for name,axs in found.items():
    if axs-allowed: raise SystemExit('Unpermitted axioms for '+name+': '+str(axs-allowed))
receipt={'scope':options.scope,'status':'passed',
         'theorems':{n:sorted(a) for n,a in sorted(found.items())}}
(ROOT/options.receipt).write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS_LOCAL_AXIOM_AUDIT',len(found),'theorems; this is not the final DFT theorem audit')
