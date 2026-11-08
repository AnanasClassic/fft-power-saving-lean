"""CI-only source checks. Reuse only accepted source/dependency closures and
matching object bundles; all changed modules are kernel checked from source.
Development reuse never replaces the final clean/official verification.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,zipfile
ROOT=Path(__file__).resolve().parents[1];os.chdir(ROOT)
if os.environ.get('GITHUB_ACTIONS')!='true':raise SystemExit('CI-only build; do not restore caches on the Mac')
BASE='2cbe338ecbcb256c4acec9120d5d0e440f982937';ARTIFACT='13628488348'
LIB=ROOT/'.lake/build/lib/lean';RECEIPT=ROOT/'.lake/build/ci-incremental.json'
accepted=set(json.loads((ROOT/'certificates/ci_physical_primitives.json').read_text())['accepted_modules'])
seed_path=ROOT/'.lake/build/ci-baseline-objects.json'
seed=json.loads(seed_path.read_text()) if seed_path.exists() else {}
source={};deps={};same={};fingerprints={};order=[]
def object_digest(mod):
    h=hashlib.sha256()
    for suffix in ['.olean','.olean.private','.olean.server']:
        p=LIB/(mod.replace('.','/')+suffix)
        h.update(suffix.encode());h.update(p.read_bytes() if p.exists() else b'MISSING')
    return h.hexdigest()
def unchanged_at(mod,commit):
    key=(mod,commit)
    if key not in same:
        p=mod.replace('.','/')+'.lean'
        old=subprocess.run(['git','show',commit+':'+p],capture_output=True)
        same[key]=old.returncode==0 and old.stdout==source[mod] and all(unchanged_at(d,commit) for d in deps[mod])
    return same[key]
def visit(mod):
    if mod in source:return
    if not re.fullmatch(r'Submission(?:\.[A-Za-z0-9_]+)*',mod):raise SystemExit('Invalid module '+mod)
    s=(ROOT/(mod.replace('.','/')+'.lean')).read_bytes();source[mod]=s
    ds=[]
    for line in s.decode().splitlines():
        if line.startswith('import '):ds.extend(x for x in line[7:].split() if x.startswith('Submission.'))
    deps[mod]=ds
    for d in ds:visit(d)
    h=hashlib.sha256(b'lean4.34.1;mathlib:d13f23b723b8a846827a245b89c10fc7d3f11612;'+s)
    for d in ds:h.update(fingerprints[d].encode())
    fingerprints[mod]=h.hexdigest();order.append(mod)
for target in sys.argv[1:] or os.environ['LEAN_DEV_TARGETS'].split():visit(target)
old=json.loads(RECEIPT.read_text()) if RECEIPT.exists() else {}
def reusable(m):
    if not (LIB/(m.replace('.','/')+'.olean')).exists():return False
    entry=old.get(m,{})
    digest=object_digest(m)
    if isinstance(entry,dict) and entry.get('fingerprint')==fingerprints[m] and entry.get('objects')==digest:return True
    # v1 saved this fingerprint and the corresponding object in the same
    # immutable cache archive. Bind its object digest when migrating to v2.
    if isinstance(entry,str) and entry==fingerprints[m]:return True
    entry=seed.get(m)
    return entry is not None and entry['objects']==digest and unchanged_at(m,entry['commit'])
need=[m for m in order if not reusable(m) and m in accepted and unchanged_at(m,BASE)]
if need:
    archive=Path('/tmp/fft-accepted-project-proofs.zip')
    with archive.open('wb') as out:
        result=subprocess.run(['gh','api','repos/AnanasClassic/fft-power-saving-lean/actions/artifacts/'+ARTIFACT+'/zip'],stdout=out)
    if result.returncode==0:
        with zipfile.ZipFile(archive) as z:
            names=set(z.namelist())
            for m in need:
                rel=m.removeprefix('Submission.').replace('.','/')
                if rel+'.olean' not in names:continue
                for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
                    name=rel+suffix
                    if name in names:
                        dst=LIB/'Submission'/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(z.read(name))
                if (LIB/(m.replace('.','/')+'.olean')).exists():
                    old[m]={'fingerprint':fingerprints[m],'objects':object_digest(m),'source_receipt':BASE}
    else:print('Old baseline artifact unavailable; missing modules will be checked from source',flush=True)
    archive.unlink(missing_ok=True)
results=[];failed=set()
env={k:v for k,v in os.environ.items() if not any(w in k.upper() for w in ['TOKEN','SECRET'])}
try:
    for m in order:
        if any(d in failed for d in deps[m]):
            failed.add(m);results.append({'module':m,'status':'blocked_by_failed_dependency'});continue
        if reusable(m):
            old[m]={'fingerprint':fingerprints[m],'objects':object_digest(m)}
            results.append({'module':m,'status':'reused_exact_source_dependencies_and_object_bundle'});continue
        dst=LIB/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
        print('CHECK_SOURCE',m,flush=True)
        p=subprocess.run(['lake','env','lean','-DautoImplicit=false',m.replace('.','/')+'.lean','-o',str(dst)],env=env)
        if p.returncode:
            failed.add(m);old.pop(m,None);results.append({'module':m,'status':'failed','exit_code':p.returncode})
            print('::error title=Lean development failure::'+m+' failed; inspect compiler output',flush=True)
        else:
            old[m]={'fingerprint':fingerprints[m],'objects':object_digest(m)}
            results.append({'module':m,'status':'kernel_accepted_current_source'})
finally:
    RECEIPT.parent.mkdir(parents=True,exist_ok=True);RECEIPT.write_text(json.dumps(old,indent=2)+'\n')
    Path('ci-incremental-result.json').write_text(json.dumps({'kind':'development-only; not official verification','baseline':BASE,'results':results},indent=2)+'\n')
if failed:raise SystemExit('FAILED_OR_BLOCKED: '+', '.join(sorted(failed)))
print('PASS_INCREMENTAL_DEVELOPMENT_CHECKS',len(order),'modules',flush=True)
