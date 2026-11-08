"""Reconstruct the two schedule edits on the pinned owned772 word.

Edit A follows DreamingOfClouds' PR6144 helper732 schedule; edit B follows
Ali Romman's PR6167 retained operand, using register 794. This is a new
reconstruction; its hash differs from the unavailable research archive.
"""
from pathlib import Path
import gzip,json,copy,hashlib,io
ROOT=Path(__file__).resolve().parents[1]
BASE_SHA='44e8ef6bfd6fd0aae5252861534b968f241f3f48b7f9266be2e981bf84a219a8'

def construct():
    raw=gzip.decompress((ROOT/'research/vendor/owned772-WORD.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest()!=BASE_SHA: raise ValueError('Base source digest')
    w=json.loads(raw)
    pr=w['program']
    removed=[['ADD',569,732,'-4',3],['ADD',576,732,'-4',3],['ADD',575,732,'-4',3],['MOVE',732,3,594,False],['ADD',732,771,'1',594],['MOVE',732,594,117,False]]
    for e in removed:
        if pr.count(e)!=1: raise ValueError('Nonunique removed source event: '+str(e))
    replace={
     tuple(['INIT',771,541]): removed[:3]+[['MOVE',732,3,117,False],['INIT',771,541]],
     tuple(['ADD',629,771,'2',117]): [['ADD',629,771,'2',117],['ADD',732,771,'1',117]],
     tuple(['MOVE',451,3,737,False]): [['MOVE',451,3,595,False]],
     tuple(['ADD',451,228,'1',737]): [['INIT',794,737],['COPY',794,228,'1',737]],
     tuple(['MOVE',772,520,737,True]): [],
     tuple(['ADD',451,772,'-4',737]): [],
     tuple(['MOVE',772,737,595,True]): [['MOVE',772,520,595,True],['ADD',451,772,'-4',595],['MOVE',451,595,737,False],['ADD',451,794,'1',737],['CLEAR',794,737]],
    }
    for e in replace:
        if sum(tuple(x)==e for x in pr)!=1: raise ValueError('Nonunique replacement source event: '+str(e))
    out=[]
    for e in pr:
     if e in removed: continue
     out+=copy.deepcopy(replace.get(tuple(e),[e]))
    v=copy.deepcopy(w);v['program']=out
    return v

def main():
    v=construct()
    raw=json.dumps(v,sort_keys=True,separators=(',',':')).encode()
    buffer=io.BytesIO()
    with gzip.GzipFile(filename='',mode='wb',fileobj=buffer,mtime=0) as out: out.write(raw)
    (ROOT/'certificates/modified-native.json.gz').write_bytes(buffer.getvalue())
    print('RECONSTRUCTED_NATIVE',len(v['program']),hashlib.sha256(raw).hexdigest())

if __name__=='__main__': main()
