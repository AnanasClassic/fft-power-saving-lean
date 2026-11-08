"""Bind a restored clean-CI object bundle to the accepted source revision.
Used only on CI, before a later development cache can overwrite any object.
"""
from pathlib import Path
import hashlib,json,os
if os.environ.get('GITHUB_ACTIONS')!='true':raise SystemExit('CI only')
root=Path(__file__).resolve().parents[1]
receipt=json.loads((root/'certificates/ci_clean_controller.json').read_text())
lib=root/'.lake/build/lib/lean'
def objects_digest(mod):
    h=hashlib.sha256()
    for suffix in ['.olean','.olean.private','.olean.server']:
        p=lib/(mod.replace('.','/')+suffix)
        h.update(suffix.encode());h.update(p.read_bytes() if p.exists() else b'MISSING')
    return h.hexdigest()
items={m:{'commit':receipt['commit'],'objects':objects_digest(m)} for m in receipt['accepted_modules']
       if (lib/(m.replace('.','/')+'.olean')).exists()}
p=root/'.lake/build/ci-baseline-objects.json';p.parent.mkdir(parents=True,exist_ok=True)
p.write_text(json.dumps(items,indent=2)+'\n')
print('Bound clean-CI object bundles to exact source revision:',len(items))
