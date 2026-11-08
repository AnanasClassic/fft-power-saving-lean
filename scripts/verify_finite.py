"""Exact finite replay, distinct from Lean certification of the finite network.

The native replay is the attributed upstream sparse validator with a declared
14-register cap. The new rational paired-controller replay retains every
input column and every stage exponent. Native calls are ideal semantic
interfaces here; the physical Lean GLiveKernelM bridge is still required.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import sys,json,gzip,hashlib,importlib.util,copy
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research/vendor'))
from native_replay import replay
from chain_check_root import family
from construct_native import construct

def need(ok,label):
    if not ok: raise ValueError(label)

def add(a,b,c=F(1)):
    out=dict(a)
    for k,v in b.items():
        out[k]=out.get(k,F(0))+c*v
        if not out[k]: del out[k]
    return out

def shifted(a,power=0,stages=()):
    out={}
    for k,v in a.items():
        col,q,*ds=k
        for s in stages: ds[s-1]+=1
        key=(col,(q+power)%4,*ds)
        out[key]=out.get(key,F(0))+v
    return {k:v for k,v in out.items() if v}

def paired_word(raw):
    need(raw['roles']==20 and raw['stages']==18,'source caller dimensions')
    events=[]
    for e in raw['events']:
        op=e[0]
        if op=='LAMBDA':
            _,r,s=e;need(s in [-1,1],'lambda sign')
            gates=[['SHIFT_P',r+20],['HI',r,r+20],['SHIFT_P',r+20],['H',r,r+20]] if s==1 else [
                ['HI',r,r+20],['SHIFT_P',r+20],['H',r,r+20],['SHIFT_P',r+20]]
            events.extend(gates)
        else:
            for offset in [0,20]:
                if op in ['ADD','SWAP','QUERY']: x=[op,e[1]+offset,e[2]+offset,*e[3:]]
                elif op=='SCALE': x=[op,e[1]+offset,e[2]]
                elif op=='LOCAL': x=[op,e[1],e[2]+offset,e[3]+offset]
                elif op=='IDLE_ONE': x=[op,e[1]+offset,e[2]]
                else: raise ValueError('unhandled raw opcode: '+op)
                events.append(x)
    return {'schema':'rational-paired-chain/1','roles':40,'stages':18,
            'proposed_ambient_rank':145,'events':events,
            'source_event_sha256':hashlib.sha256(json.dumps(raw['events'],separators=(',',':')).encode()).hexdigest()}

def check_paired(word,raw):
    rows=[{(r,0,*([0]*18)):F(1)} for r in range(40)]
    for e in word['events']:
        op=e[0]
        if op=='ADD': rows[e[1]]=add(rows[e[1]],rows[e[2]],F(e[3]))
        elif op=='SCALE': rows[e[1]]={k:F(e[2])*v for k,v in rows[e[1]].items()}
        elif op=='SWAP': rows[e[1]],rows[e[2]]=rows[e[2]],rows[e[1]]
        elif op in ['H','HI']:
            a,b=e[1:];x,y=rows[a],rows[b];c=F(1,2) if op=='HI' else F(1)
            rows[a]={k:c*v for k,v in add(x,y).items()}
            rows[b]={k:c*v for k,v in add(x,y,F(-1)).items()}
        elif op=='SHIFT_P': rows[e[1]]=shifted(rows[e[1]],2)
        elif op=='QUERY': rows[e[1]]=add(rows[e[1]],shifted(rows[e[2]],e[3]))
        elif op=='LOCAL':
            _,stage,src,dst=e
            rows[dst]=add(rows[dst],shifted(rows[src],-1))
            for r in [src,dst]: rows[r]=shifted(rows[r],stages=[stage])
        elif op=='IDLE_ONE': rows[e[1]]=shifted(rows[e[1]],stages=e[2])
        else: raise ValueError(op)
    for r,row in enumerate(rows):
        d=raw['diagonal'][r%20]
        need(d[1]==0,'unused degree coordinate')
        need(row=={(r,d[0]%4,*d[2:]):F(1)},f'paired endpoint row {r}')
    return {'roles':40,'independent_matrix_entries':1600,'events':len(word['events']),
            'ring':'Q[q,D1,...,D18]/(q^4-1); no reduction of stage exponents',
            'endpoint':'each independent input r maps to q^-1 times its stage monomial',
            'macro_counts':dict(sorted(Counter(e[0] for e in word['events']).items()))}

def main():
    native=construct()
    native_result=replay(native)
    paid={int(k):v for k,v in native_result['local_paid'].items()}
    helpers={int(k):v for k,v in native_result['local_helpers'].items()}
    raw=json.loads((ROOT/'research/vendor/chain-CALLER.json').read_text())
    root=family(raw)
    word=paired_word(raw)
    paired=check_paired(word,raw)
    need(len(word['events'])==2598,'paired macro count')
    inv=json.loads((ROOT/'inventory_receipt.json').read_text())
    PT=Counter();PP=Counter()
    for e in word['events']:
        if e[0]=='LOCAL':
            for r,n in paid.items(): PP[r]+=n # one complete 104-port native invocation
        elif e[0]=='QUERY': PP[1]+=104
        elif e[0]=='IDLE_ONE': PP[8*len(e[2])]+=104
    # A LOCAL is one full supplier with all 104 ports and its helper outputs.
    # Helpers belong to each supplier once, rather than once per port.
    PT=Counter({r:36*n for r,n in helpers.items()})
    for d in raw['diagonal']: PT[1+8*sum(d[2:])]+=2*104
    need(dict(PT)=={int(k):v for k,v in inv['T'].items()},'word-derived productive histogram')
    need(dict(PP)=={int(k):v for k,v in inv['P'].items()},'word-derived paid histogram')
    need((native_result['peak_owned'],native_result['events'])==(14,22836),'native resources')
    # Rejection controls exercise the actual validators, including -O execution.
    faults=[]
    for label,mutate in [
        ('wrong_query',lambda w: next(e for e in w['events'] if e[0]=='QUERY').__setitem__(3,1)),
        ('missing_normalizer_gate',lambda w: w['events'].pop(next(i for i,e in enumerate(w['events']) if e[0]=='HI'))),
        ('wrong_idle',lambda w: next(e for e in w['events'] if e[0]=='IDLE_ONE')[2].pop())]:
        broken=copy.deepcopy(word);mutate(broken)
        try: check_paired(broken,raw)
        except ValueError: faults.append(label)
        else: raise ValueError('accepted faulty controller: '+label)
    bad=copy.deepcopy(native)
    pos=next(i for i,e in enumerate(bad['program']) if e==['ADD',451,794,'1',737])
    bad['program'][pos][3]='-1'
    try: replay(bad)
    except ValueError: faults.append('wrong_retained_operand_sign')
    else: raise ValueError('accepted faulty native')
    b=json.dumps(word,sort_keys=True,separators=(',',':')).encode()
    (ROOT/'certificates/paired-controller.json').write_bytes(b+b'\n')
    keys=['events','operations','rows_checked','endpoint_coefficients','owned_fields','owned_lifetimes',
          'peak_owned','real_scalar_allowance','local_paid','local_helpers']
    receipt={'status':'Python finite replay only','native':{k:native_result[k] for k in keys},
             'raw_controller_audit':root,'paired_controller':paired,
             'paired_payload_sha256':hashlib.sha256(b).hexdigest(),'negative_controls':faults,
             'productive_count':sum(PT.values()),'paid_count':sum(PP.values()),
             'productive_rank_mass':sum(r*n for r,n in PT.items()),
             'paid_rank_mass':sum(r*n for r,n in PP.items()),
             'unproved':'Native Clifford lift, all-width operator bridge, physical RAM realization, GLiveKernelM and cost contract'}
    (ROOT/'certificates/finite_replay.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print('PASS_FINITE_PYTHON_REPLAY',receipt['productive_count'],receipt['paid_count'],faults)

if __name__=='__main__': main()
