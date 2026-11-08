"""Local source/pin guard. It does not replace Lean or the official Comparator."""
from pathlib import Path
import json,re,hashlib
ROOT=Path(__file__).resolve().parents[1]

def code_only(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1;i+=2
            elif s.startswith('-/',i): depth-=1;i+=2
            else: i+=1
        elif quoted:
            if s[i]=='\\': i+=2
            elif s[i]=='"': quoted=False;i+=1
            else:i+=1
        elif s.startswith('/-',i): depth=1;i+=2;out.append(' ')
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j;out.append('\n')
        elif s[i]=='"': quoted=True;i+=1;out.append(' ')
        else:out.append(s[i]);i+=1
    if depth or quoted: raise ValueError('Unterminated lexical region')
    return ''.join(out)

files=[ROOT/'Submission.lean',*sorted((ROOT/'Submission').rglob('*.lean'))]
for p in files:
    code=code_only(p.read_text())
    bad=re.search(r'\b(sorry|admit|axiom|native_decide|sorryAx)\b|debug\.skipKernelTC',code)
    if bad:raise SystemExit(f'Forbidden proof shortcut in {p}: {bad.group()}')
pins=json.loads((ROOT/'certificates/source_pins.json').read_text())
for name,pin in pins['files'].items():
    p=ROOT/name
    if hashlib.sha256(p.read_bytes()).hexdigest()!=pin['sha256']:
        raise SystemExit('Pinned source bytes changed: '+name)
    if 'prefix_sha256' in pin:
        if hashlib.sha256(p.read_bytes()[:pin['prefix_bytes']]).hexdigest()!=pin['prefix_sha256']:
            raise SystemExit('Trusted model prefix changed')
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
if mathlib['rev']!=pins['sources']['mathlib']['commit']:raise SystemExit('Mathlib pin mismatch')
if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise SystemExit('Toolchain mismatch')
print('PASS_LOCAL_SOURCE_GUARD',len(files),'Lean files; final theorem presence is a separate gate')
