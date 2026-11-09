#!/usr/bin/env python3
"""Pinned exact-DFT research probe; no claim that delta=.005 is attained.
Uses the credited PR6934 word as INPUT, not as a new construction.
The helper split criterion is Ali Romman's PR5599. Modular nullspaces are
search only; every exported candidate is checked over Q. No upstream code runs.
"""
from __future__ import annotations
import argparse, copy, gzip, hashlib, json, math, time, urllib.request
from collections import Counter, defaultdict
from fractions import Fraction as Q
from pathlib import Path
PIN='4e13b7acdbea1c9f12aa88126435360eecea7401'
BASE='https://raw.githubusercontent.com/DreamingOfClouds/integer-mult-bounds/'+PIN+'/research/p104-shared-odd-native/'
MOD=2305843009213693951
START=time.monotonic()
def need(p,msg):
    if not p: raise ValueError(msg)
def fetch(root,name):
    p=root/name; p.parent.mkdir(parents=True,exist_ok=True)
    if not p.exists():
        with urllib.request.urlopen(BASE+name,timeout=60) as r: data=r.read()
        p.write_bytes(data)
    data=p.read_bytes()
    print('SOURCE',name,len(data),hashlib.sha256(data).hexdigest(),flush=True)
    return json.loads(gzip.decompress(data) if name.endswith('.gz') else data)
def span(b):
    out={0}
    for x in b:
        need(isinstance(x,int) and 0<x<512 and x not in out,'frame basis')
        out |= {y^x for y in out}
    return frozenset(out)
def main_roles(w):
    live=set(w['live']); h=w.get('hosted',{})
    return live | {r+112 for r in live} | set(h.get('X2',[])) | set(h.get('Y2',[]))
def native_profiles(w):
    mains=main_roles(w); ds=list(map(len,w['frames']))
    h=Counter(ds[v]-ds[u] for r,(u,v) in enumerate(zip(w['initial'],w['final'])) if r not in mains)
    p=Counter(abs(ds[e[3]]-ds[e[2]]) for e in w['program'] if e[0]=='MOVE')
    return h,p
def invoice(w,j):
    h,p=native_profiles(w); t=Counter(); paid=Counter()
    nt={k:len(v['ports']) for k,v in j['types'].items()}
    for e in j['events']:
        if e[0]=='J':t.update(h);paid.update(p)
        elif e[1]=='QUERY':paid[1]+=nt[e[0]]
        elif e[1]=='IDLE_ONE':paid[8*len(e[3])]+=nt[e[0]]
    for ty,v in j['types'].items():
        for d in v['diagonal']: t[d[0]%2+8*sum(d[2:])]+=nt[ty]
    return t,paid
def moment(t,p,d=.005):
    return math.fsum(c*r**(1-d) for r,c in t.items())-math.fsum(c*r**(1-d) for r,c in p.items())
def rawroot(t,p):
    lo,hi=0.,.05
    need(moment(t,p,lo)>0,'positive rank surplus')
    for _ in range(60):
        m=(lo+hi)/2
        if moment(t,p,m)>0:lo=m
        else:hi=m
    return (lo+hi)/2

def axpy(dst,src,q,mod=None):
    if not q:return
    for k,v in src.items():
        v=dst.get(k,0)+q*v
        if mod:v%=mod
        if v:dst[k]=v
        else:dst.pop(k,None)
def scaled(v,q,mod=None):
    if mod:return {k:x*q%mod for k,x in v.items() if x*q%mod}
    return {k:x*q for k,x in v.items() if x*q}
def scalar(e,mod=None):
    q=Q(e[2] if e[0]=='SCALE' else e[3])
    return q if mod is None else q.numerator%mod*pow(q.denominator,-1,mod)%mod
def forward(rows,e,mod=None):
    op,r=e[:2]
    if op=='MOVE':return
    if op in ('INIT','CLEAR'):rows[r]={};return
    q=scalar(e,mod)
    if op=='SCALE':rows[r]=scaled(rows[r],q,mod)
    elif op in ('ADD','COPY'):
        if op=='COPY': rows[r]={}
        axpy(rows[r],rows[e[2]],q,mod)
    else:raise ValueError(op)
def reverse(cols,e,mod=None):
    op,r=e[:2]
    if op=='MOVE':return
    if op in ('INIT','CLEAR'):cols[r]={};return
    q=scalar(e,mod)
    if op=='SCALE':cols[r]=scaled(cols[r],q,mod)
    elif op in ('ADD','COPY'):
        axpy(cols[e[2]],cols[r],q,mod)
        if op=='COPY':cols[r]={}
    else:raise ValueError(op)
def expected(w):
    n=len(w['initial']); h=w['hosted']; x=set(w['live']); y={r+112 for r in x}
    dx={w['live'][i] for i in h['Dports']}; pairs=dict(zip(h['X2'],h['Y2']))
    out=[]
    for r in range(n+w['owned_fields']):
        if r>=n:v={}
        elif r in x:v={r:Q(1)} if r in dx else {r:Q(1),r+112:Q(h['alpha'])}
        elif r in y:v={r-112:Q(1),r:Q(1)} if r-112 in dx else {r-112:Q(h['beta']),r:1+Q(h['alpha'])*Q(h['beta'])}
        elif r in pairs:v={r:Q(1),pairs[r]:Q(h['alpha2'])}
        else:v={r:Q(1)}
        out.append({k:x for k,x in v.items() if x})
    return out
def exact_replay(w):
    n=len(w['initial']); nr=n+w['owned_fields']; rows=[({r:Q(1)} if r<n else {}) for r in range(nr)]
    cur=list(w['initial'])+[None]*w['owned_fields']; ss=list(map(span,w['frames'])); active=set()
    for i,e in enumerate(w['program']):
        op,r=e[:2]
        if op=='MOVE':
            a,b,pv=e[2:];need(cur[r]==a and bool(pv)==(r in active),('move state',i))
            need(ss[a]<ss[b] or (pv and ss[b]<ss[a]),('move nesting',i));cur[r]=b
        elif op=='INIT':need(r>=n and r not in active,('init',i));active.add(r);cur[r]=e[2]
        elif op=='CLEAR':need(r in active and cur[r]==e[2],('clear',i));active.remove(r);cur[r]=None
        elif op=='SCALE':need(cur[r]==e[-1] and Q(e[2])!=0,('scale',i))
        else:
            need(cur[r]==cur[e[2]]==e[-1] and r!=e[2],('contact',i))
            if op=='COPY':need(r in active and not rows[r],('copy',i))
        forward(rows,e)
        if i and i%20000==0:print('EXACT_PREFIX',i,'elapsed',round(time.monotonic()-START,2),flush=True)
    need(not active and cur[:n]==w['final'],'final frames')
    need(rows==expected(w),'exact endpoint')
    return {'public':n,'owned':w['owned_fields'],'events':len(w['program']),'endpoint':'exact rational PASS','all_width_physical_proof':'NOT CHECKED HERE'}
def kernel_combinations(rows,group,mod=MOD):
    piv={}; out=[]
    for i,row in enumerate(rows):
        v={k:x for k,x in row.items() if k not in group}; c={i:1}
        while v:
            k=min(v); x=v[k]
            if k not in piv:
                q=pow(x,-1,mod);piv[k]=(scaled(v,q,mod),scaled(c,q,mod));break
            u,a=piv[k];axpy(v,u,-x,mod);axpy(c,a,-x,mod)
        if not v:out.append(c)
    return out
def combine(cs,rows,mod=None):
    out={}
    for i,q in cs.items():axpy(out,rows[i],q,mod)
    return out
def dot(a,b,mod=None):
    v=sum(x*b.get(k,0) for k,x in a.items())
    return v%mod if mod else v
def rational_reconstruct(x,p=MOD):
    x%=p
    if not x:return Q(0)
    bound=math.isqrt(p//2); a,b=p,x; u,v=0,1
    while abs(b)>bound:
        q=a//b;a,b=b,a-q*b;u,v=v,u-q*v
    if v and abs(v)<=bound and math.gcd(b,v)==1:
        f=Q(b,v)
        if (f.numerator-x*f.denominator)%p==0:return f
    raise ValueError('rational reconstruction failed')
def exact_cut(w,candidate):
    a={r:rational_reconstruct(x) for r,x in candidate['a'].items()}
    b={r:rational_reconstruct(x) for r,x in candidate['b'].items()}
    n=len(w['initial']);nr=n+w['owned_fields'];cut=candidate['cut'];g=set(candidate['group'])
    c=dict(a)
    for e in reversed(w['program'][:cut]):
        op,r=e[:2];q=scalar(e) if op in ('ADD','COPY','SCALE') else None
        if op in ('INIT','CLEAR'):c.pop(r,None)
        elif op=='SCALE':
            if r in c:c[r]*=q
        elif op in ('ADD','COPY'):
            v=c.get(e[2],0)+q*c.get(r,0)
            if v:c[e[2]]=v
            else:c.pop(e[2],None)
            if op=='COPY':c.pop(r,None)
    d=[Q(0)]*nr
    for r,v in b.items():d[r]=v
    for e in w['program'][cut:]:
        op,r=e[:2]
        if op in ('INIT','CLEAR'):d[r]=Q(0)
        elif op=='SCALE':d[r]*=scalar(e)
        elif op in ('ADD','COPY'):
            if op=='COPY':d[r]=Q(0)
            d[r]+=scalar(e)*d[e[2]]
    d={r:v for r,v in enumerate(d) if v}
    need(set(c)<=g and set(d)<=g,'helper-only prefix/suffix')
    z=dot(a,b);need(z and z==dot(c,d),'equal nonzero pairings')
    b=scaled(b,1/z);d=scaled(d,1/z)
    return {**candidate,'a':a,'b':b,'c':c,'d':d,'verified':'exact rational split identities only'}
def split_scan(w,budget=200.,max_group=96):
    n=len(w['initial']);nr=n+w['owned_fields']; ss=list(map(span,w['frames']));ds=list(map(len,w['frames'])); mains=main_roles(w)
    groups=defaultdict(set)
    for r,(u,v) in enumerate(zip(w['initial'],w['final'])):
        if r not in mains and ds[v]-ds[u]>1:groups[u,v].add(r)
    group_of={r:g for g,rs in groups.items() for r in rs}
    print('BOUNDARY_GROUPS',[(g,len(rs)) for g,rs in sorted(groups.items(),key=lambda x:-len(x[1]))[:15]],flush=True)
    cur=list(w['initial'])+[None]*w['owned_fields']; members=defaultdict(set)
    for r,f in enumerate(cur):
        if f is not None:members[f].add(r)
    rows=[({r:1} if r<n else {}) for r in range(nr)]; snapshots=defaultdict(list); seen=0; started=time.monotonic()
    for i,e in enumerate(w['program']):
        if time.monotonic()-started>budget:break
        op,r=e[:2];changed=set()
        if op in ('MOVE','INIT','CLEAR'):
            old=cur[r];new=e[3] if op=='MOVE' else (e[2] if op=='INIT' else None)
            if old is not None:members[old].discard(r);changed.add(old)
            if new is not None:members[new].add(r);changed.add(new)
            cur[r]=new
        elif op=='COPY':changed.add(cur[r])
        forward(rows,e,MOD)
        for f in changed:
            if f is None or not 0<ds[f]<9:continue
            rs=sorted(members[f])
            if not rs or len(rs)>max_group:continue
            rr=[rows[r] for r in rs]
            eligible={group_of[r] for r in rs if r in group_of and ss[group_of[r][0]]<ss[f]<ss[group_of[r][1]]}
            for g in eligible:
                seen+=1; A=kernel_combinations(rr,groups[g]);C=[combine(a,rr,MOD) for a in A]
                if not any(C):continue
                snapshots[i+1].append({'frame':f,'roles':rs,'g':g,'A':A,'C':C})
        if i and i%20000==0:print('FORWARD_SCAN',i,'cuts',len(snapshots),'tested',seen,flush=True)
    covered=i+1
    print('PREFIX_SCAN_DONE',covered,'/',len(w['program']),'stored',sum(map(len,snapshots.values())),flush=True)
    cols=[({r:1} if r<n else {}) for r in range(nr)]; found=[]; tested=0
    for cut in range(len(w['program']),-1,-1):
        for rec in snapshots.get(cut,[]):
            rs=rec['roles'];g=groups[rec['g']];sr=[cols[r] for r in rs];B=kernel_combinations(sr,g);D=[combine(b,sr,MOD) for b in B]
            tested+=1
            for a,c in zip(rec['A'],rec['C']):
                uv=[(dot(a,b,MOD),dot(c,d,MOD)) for b,d in zip(B,D)]
                chosen=None
                for j,(u,v) in enumerate(uv):
                    if u and u==v:chosen=B[j];break
                if chosen is None:
                    for j,(u,v) in enumerate(uv):
                        wj=(u-v)%MOD
                        for k in range(j):
                            uk,vk=uv[k];wk=(uk-vk)%MOD
                            if (u*wk-uk*wj)%MOD:
                                chosen=scaled(B[j],wk,MOD);axpy(chosen,B[k],-wj,MOD);break
                        if chosen is not None:break
                if chosen is not None:
                    u,v=rec['g'];f=rec['frame']
                    found.append({'cut':cut,'frame':f,'initial_frame':u,'final_frame':v,'group':sorted(g),'roles':rs,'a':{rs[j]:x for j,x in a.items()},'b':{rs[j]:x for j,x in chosen.items()},'gain_at_005':(ds[f]-ds[u])**.995+(ds[v]-ds[f])**.995-(ds[v]-ds[u])**.995})
                    break
        if cut:reverse(cols,w['program'][cut-1],MOD)
    print('MODULAR_SPLIT_SEARCH',{'covered_prefix':covered,'candidate_groups_tested':seen,'suffix_tests':tested,'candidates':len(found)},flush=True)
    found.sort(key=lambda x:-x['gain_at_005']);exact=[]
    for cand in found[:100]:
        try:exact.append(exact_cut(w,cand))
        except ValueError:continue
        if len(exact)>=8:break
    print('EXACT_ADDITIONAL_SPLITS',len(exact),'best_gain',exact[0]['gain_at_005'] if exact else None,flush=True)
    return {'covered_prefix':covered,'total_events':len(w['program']),'scanned_boundary_groups':seen,'modular_candidates':len(found),'exact_candidates':exact}
def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x
def run():
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='research/delta005/out');ap.add_argument('--budget',type=float,default=180);args=ap.parse_args()
    root=Path(args.output);root.mkdir(parents=True,exist_ok=True)
    w=fetch(root,'data/word.json.gz');j=fetch(root,'data/caller.json')
    rep=exact_replay(w);t,p=invoice(w,j);h,lp=native_profiles(w)
    ideal=Counter(t)
    for r,c in h.items():ideal[r]-=18*c;ideal[1]+=18*c*r
    report={'source_pin':PIN,'source_status':'PR6934 conditional predecessor; not a DFT theorem','replay':rep,'helpers':h,'local_paid':lp,'targets':t,'paid':p,'raw_root_heuristic':rawroot(t,p),'margin_005_heuristic':moment(t,p),'surplus':sum(r*c for r,c in t.items())-sum(r*c for r,c in p.items()),'all_helper_rank1_relaxation_margin_005':moment(ideal,p),'all_helper_rank1_relaxation_root':rawroot(ideal,p)}
    need(abs(report['raw_root_heuristic']-.0036238597350766513)<1e-11,'baseline root reproduction')
    print('BASELINE_REPORT',json.dumps(encode(report),sort_keys=True),flush=True)
    (root/'baseline.json').write_text(json.dumps(encode(report),indent=2))
    scan=split_scan(w,args.budget);(root/'split_scan.json').write_text(json.dumps(encode(scan),indent=2))
    print('RESEARCH_PROBE_COMPLETE: NO NEW FFT THEOREM CLAIMED',flush=True)
if __name__=='__main__':run()
