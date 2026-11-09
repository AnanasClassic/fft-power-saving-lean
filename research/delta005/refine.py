#!/usr/bin/env python3
"""Cost-aware intermediate-stop helper splitting.
Each accepted edit is certified over Q, then literally lowered to scalar
basis gates and nested MOVE instructions. Ali Romman's split identity is
credited; this is a search implementation, not a new general split theorem.
No claim of an all-width DFT theorem follows from this program alone.
"""
import argparse, copy, gzip, json, time
from collections import Counter, defaultdict
from fractions import Fraction as Q
from pathlib import Path
from probe import *

def stop_scan(w, budget=240., max_group=256):
    n=len(w['initial']); nr=n+w['owned_fields']; ss=list(map(span,w['frames'])); ds=list(map(len,w['frames'])); mains=main_roles(w)
    groups=defaultdict(set)
    for r,(u,v) in enumerate(zip(w['initial'],w['final'])):
        if r not in mains and ds[v]-ds[u]>1: groups[u,v].add(r)
    group_of={r:g for g,rs in groups.items() for r in rs}
    between={}
    for e in w['program']:
        if e[0]!='MOVE':continue
        a,b=e[2:4]
        if abs(ds[a]-ds[b])<2 or (a,b) in between:continue
        lo,hi=(a,b) if ds[a]<ds[b] else (b,a)
        between[a,b]=[f for f in range(len(ss)) if ds[lo]<ds[f]<ds[hi] and ss[lo]<ss[f]<ss[hi]]
    cur=list(w['initial'])+[None]*w['owned_fields']; members=defaultdict(set)
    for r,f in enumerate(cur):
        if f is not None:members[f].add(r)
    rows=[({r:1} if r<n else {}) for r in range(nr)]; snapshots=defaultdict(list); seen=0; start=time.monotonic()
    for i,e in enumerate(w['program']):
        if time.monotonic()-start>budget:break
        op,r=e[:2]
        if op in ('MOVE','INIT','CLEAR'):
            old=cur[r]; new=e[3] if op=='MOVE' else (e[2] if op=='INIT' else None)
            if old is not None:members[old].discard(r)
            if new is not None:members[new].add(r)
            cur[r]=new
        forward(rows,e,MOD)
        if op!='MOVE':continue
        a,b=e[2:4]
        for f in between.get((a,b),[]):
            rs=sorted(members[f]|{r})
            if len(rs)>max_group:continue
            rr=[rows[z] for z in rs]
            eligible={group_of[z] for z in rs if z in group_of and ss[group_of[z][0]]<ss[f]<ss[group_of[z][1]]}
            debit=abs(ds[a]-ds[f])**.995+abs(ds[b]-ds[f])**.995-abs(ds[a]-ds[b])**.995
            for g in eligible:
                u,v=g
                gain=(ds[f]-ds[u])**.995+(ds[v]-ds[f])**.995-(ds[v]-ds[u])**.995-debit
                if gain<1e-12:continue
                seen+=1; A=kernel_combinations(rr,groups[g]); C=[combine(x,rr,MOD) for x in A]
                if not any(C):continue
                snapshots[i+1].append({'frame':f,'roles':rs,'g':g,'A':A,'C':C,'gain':gain,'stop_debit':debit,'move':e})
        if i and i%20000==0:print('STOP_PREFIX',i,'tests',seen,'stored',sum(map(len,snapshots.values())),flush=True)
    covered=i+1
    cols=[({r:1} if r<n else {}) for r in range(nr)];found=[]
    for cut in range(len(w['program']),-1,-1):
        for rec in snapshots.get(cut,[]):
            rs=rec['roles']; g=groups[rec['g']]; sr=[cols[z] for z in rs]; B=kernel_combinations(sr,g); D=[combine(x,sr,MOD) for x in B]
            for a,c in zip(rec['A'],rec['C']):
                uv=[(dot(a,b,MOD),dot(c,d,MOD)) for b,d in zip(B,D)]; chosen=None
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
                    found.append({'cut':cut,'frame':f,'initial_frame':u,'final_frame':v,'group':sorted(g),'roles':rs,'a':{rs[k]:x for k,x in a.items()},'b':{rs[k]:x for k,x in chosen.items()},'gain_at_005':rec['gain'],'extra_stop':rec['move'],'stop_debit_at_005':rec['stop_debit']});break
        if cut:reverse(cols,w['program'][cut-1],MOD)
    found.sort(key=lambda x:-x['gain_at_005']); exact=[]
    for cand in found[:500]:
        try:exact.append(exact_cut(w,cand))
        except ValueError:continue
        if len(exact)>=8:break
    print('STOP_SCAN',json.dumps({'covered':covered,'events':len(w['program']),'tests':seen,'snapshots':sum(map(len,snapshots.values())),'modular_candidates':len(found),'exact_candidates':len(exact),'best_net_gain':exact[0]['gain_at_005'] if exact else None}),flush=True)
    return exact,{'covered':covered,'events':len(w['program']),'tests':seen,'modular_candidates':len(found),'exact_candidates':len(exact)}

def basis_gates(a,b,p,f):
    need(dot(a,b)==1,'basis unit pairing')
    j=next(iter(b)); bj=b[j]; union=sorted(set(a)|set(b)|{p}); out=[]
    for r in union:
        if r!=j and b.get(r,0):out.append(['ADD',r,j,str(-b[r]/bj),f])
    if bj!=1:out.append(['SCALE',j,str(1/bj),f])
    for r in union:
        if r!=j and a.get(r,0):out.append(['ADD',j,r,str(a[r]),f])
    if p!=j:
        out.extend([['ADD',p,j,'1',f],['ADD',j,p,'-1',f],['ADD',p,j,'1',f],['SCALE',j,'-1',f]])
    return out

def inverse_gates(ops):
    out=[]
    for e in reversed(ops):
        e=list(e)
        if e[0]=='SCALE':e[2]=str(1/Q(e[2]))
        elif e[0]=='ADD':e[3]=str(-Q(e[3]))
        else:raise ValueError('nonordinary inverse')
        out.append(e)
    return out

def rename(ops,n,p=None,z=None):
    out=[]
    def r(x):
        x=x+1 if x>=n else x
        return z if p is not None and x==p else x
    for e in ops:
        e=list(e);e[1]=r(e[1])
        if e[0] in ('ADD','COPY'):e[2]=r(e[2])
        out.append(e)
    return out

def apply_split(w,c):
    w=copy.deepcopy(w);n=len(w['initial']);p=min(set(c['roles'])&set(c['group']));z=n
    u,v,f=c['initial_frame'],c['final_frame'],c['frame'];cut=c['cut']
    G=basis_gates(c['c'],c['d'],p,u);J=basis_gates(c['a'],c['b'],p,f)
    Gout=[e[:-1]+[v] for e in G]
    before=w['program'][:cut];after=w['program'][cut:]
    if 'extra_stop' in c:
        e=c['extra_stop'];need(before[-1]==e,'stop source')
        first=list(e);first[3]=f;second=list(e);second[2]=f
        before=before[:-1]+[first];after=[second]+after
    w['program']=(rename(inverse_gates(G),n)+rename(before,n)+rename(J,n)+rename(inverse_gates(J),n,p,z)+rename(after,n,p,z)+rename(Gout,n,p,z))
    w['initial'].append(f);w['final'][p]=f;w['final'].append(v)
    w.setdefault('delta005_split_history',[]).append(encode(c))
    return w

def selftest():
    import random
    rng=random.Random(20261109)
    for _ in range(100):
        k=6;a={i:Q(rng.randint(-3,3)) for i in range(k)};b={i:Q(rng.randint(-3,3)) for i in range(k)}
        a={i:x for i,x in a.items() if x};b={i:x for i,x in b.items() if x};z=dot(a,b)
        if not z:continue
        b=scaled(b,1/z);p=rng.randrange(k);ops=basis_gates(a,b,p,0)
        rows=[{i:Q(1)} for i in range(k)]
        for e in ops:forward(rows,e)
        need(rows[p]==a,'basis row');need([dot(row,b) for row in rows]==[int(i==p) for i in range(k)],'basis column')
        for e in inverse_gates(ops):forward(rows,e)
        need(rows==[{i:Q(1)} for i in range(k)],'basis inverse')
    w={'initial':[0,0],'final':[2,2],'frames':[[],[1],[1,2]],'owned_fields':0,'live':[],
       'hosted':{'Dports':[],'X2':[],'Y2':[],'alpha':-1,'beta':'1/2','alpha2':-1},
       'program':[['MOVE',0,0,1,False],['MOVE',1,0,1,False],['MOVE',0,1,2,False],['MOVE',1,1,2,False]]}
    c={'cut':2,'frame':1,'initial_frame':0,'final_frame':2,'roles':[0,1],'group':[0,1], 'a':{0:Q(1)},'b':{0:Q(1)},'c':{0:Q(1)},'d':{0:Q(1)}}
    exact_replay(apply_split(w,c))
    print('SELFTEST_BASIS_AND_LITERAL_SPLICE_PASS',flush=True)

def run_refine():
    ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=32);ap.add_argument('--budget',type=float,default=120);ap.add_argument('--output',default='research/delta005/out');args=ap.parse_args()
    selftest();root=Path(args.output);w=fetch(root,'data/word.json.gz');j=fetch(root,'data/caller.json');start=time.monotonic();history=[]
    for iteration in range(args.rounds):
        cand,stats=stop_scan(w,args.budget)
        if not cand:
            history.append({'round':iteration,'search':stats,'result':'no additional positive single-stop split found'});break
        oldt,oldp=invoice(w,j);c=cand[0];nw=apply_split(w,c);nt,np=invoice(nw,j)
        predicted=18*c['gain_at_005'];observed=moment(nt,np)-moment(oldt,oldp)
        need(abs(predicted-observed)<1e-7,'charged moment change')
        oldh,oldlp=native_profiles(w);newh,newlp=native_profiles(nw)
        need(sum(newh.values())==sum(oldh.values())+1,'one independent input added')
        need(sum(r*(nt[r]-np[r]) for r in set(nt)|set(np))==1520,'rank surplus unchanged')
        w=nw;entry={'round':iteration,'root_heuristic':rawroot(nt,np),'margin_005_heuristic':moment(nt,np),'gain_005':observed,'cut':c['cut'],'frame':c['frame'],'search':stats};history.append(entry)
        print('ACCEPTED_EXACT_SPLIT',json.dumps(entry,sort_keys=True),flush=True)
        (root/'refinement_history.json').write_text(json.dumps(encode(history),indent=2))
        (root/'refined-word.json.gz').write_bytes(gzip.compress(json.dumps(encode(w),separators=(',',':')).encode(),mtime=0))
        if iteration%8==7:exact_replay(w)
        if moment(nt,np,.00500001)>0:break
        if time.monotonic()-start>600:break
    rep=exact_replay(w);t,p=invoice(w,j)
    report={'history':history,'exact_replay':rep,'targets':t,'paid':p,'raw_root_heuristic':rawroot(t,p),'margin_005_heuristic':moment(t,p),'statement':'Finite normalized identities only. No all-width/DFT theorem claimed.'}
    (root/'refinement.json').write_text(json.dumps(encode(report),indent=2));print('FINAL_REFINEMENT',json.dumps(encode(report),sort_keys=True),flush=True)
if __name__=='__main__':run_refine()
