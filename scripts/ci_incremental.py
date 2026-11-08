"""Incremental development checks on CI only; final verification stays separate.
Reuse a proof object only when the source and every project dependency match
its previously kernel-accepted revision. All changed modules are re-elaborated.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,zipfile
ROOT=Path(__file__).resolve().parents[1]
os.chdir(ROOT)
BASE='2cbe338ecbcb256c4acec9120d5d0e440f982937'
ARTIFACT='13628488348'
LIB=ROOT/'.lake/build/lib/lean'
RECEIPT=ROOT/'.lake/build/ci-incremental.json'
accepted=set(json.loads((ROOT/'certificates/ci_physical_primitives.json').read_text())['accepted_modules'])
source={};deps={};baseline={};fingerprints={};order=[]

def visit(mod):
    if mod in source:return
    if not re.fullmatch(r'Submission(?:\.[A-Za-z0-9_]+)+',mod):
        raise SystemExit('Invalid project module '+mod)
    p=ROOT/(mod.replace('.','/')+'.lean')
    s=p.read_bytes();source[mod]=s
    ds=[]
    for line in s.decode().splitlines():
        if line.startswith('import '):
            ds.extend(x for x in line[7:].split() if x.startswith('Submission.'))
    deps[mod]=ds
    for d in ds:visit(d)
    old=subprocess.run(['git','show',BASE+':'+str(p.relative_to(ROOT))],capture_output=True)
    baseline[mod]=mod in accepted and old.returncode==0 and old.stdout==s and all(baseline[d] for d in ds)
    h=hashlib.sha256(b'lean4.34.1;mathlib:d13f23b723b8a846827a245b89c10fc7d3f11612;'+s)
    for d in ds:h.update(fingerprints[d].encode())
    fingerprints[mod]=h.hexdigest();order.append(mod)

targets=sys.argv[1:] or os.environ['LEAN_DEV_TARGETS'].split()
for target in targets:visit(target)
old=json.loads(RECEIPT.read_text()) if RECEIPT.exists() else {}
need_base=[m for m in order if baseline[m] and not (LIB/(m.replace('.','/')+'.olean')).exists()]
if need_base:
    archive=Path('/tmp/fft-accepted-project-proofs.zip')
    with archive.open('wb') as out:
        subprocess.run(['gh','api','repos/AnanasClassic/fft-power-saving-lean/actions/artifacts/'+ARTIFACT+'/zip'],stdout=out,check=True)
    with zipfile.ZipFile(archive) as z:
        for m in need_base:
            rel=m.removeprefix('Submission.').replace('.','/')
            for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
                name=rel+suffix
                if name in z.namelist():
                    dst=LIB/'Submission'/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(z.read(name))
    archive.unlink()
results=[]
try:
    for m in order:
        dst=LIB/(m.replace('.','/')+'.olean')
        if dst.exists() and (baseline[m] or old.get(m)==fingerprints[m]):
            results.append({'module':m,'status':'reused_exact_source_and_dependencies'});continue
        dst.parent.mkdir(parents=True,exist_ok=True)
        print('CHECK_SOURCE',m,flush=True)
        result=subprocess.run(['lake','env','lean','-DautoImplicit=false',m.replace('.','/')+'.lean','-o',str(dst)])
        if result.returncode:
            results.append({'module':m,'status':'failed'});raise SystemExit(result.returncode)
        old[m]=fingerprints[m]
        results.append({'module':m,'status':'kernel_accepted_current_source'})
finally:
    RECEIPT.parent.mkdir(parents=True,exist_ok=True);RECEIPT.write_text(json.dumps(old,indent=2)+'\n')
    Path('ci-incremental-result.json').write_text(json.dumps({'kind':'development-only; not official verification','baseline':BASE,'results':results},indent=2)+'\n')
print('PASS_INCREMENTAL_DEVELOPMENT_CHECKS',len(order),'modules',flush=True)
