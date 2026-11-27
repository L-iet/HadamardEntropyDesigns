"""Exact base certificate and tensor checks, using only the standard library."""
from itertools import combinations, product
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'exchanges'))
from cube_kernel import cube_kernel


def row(mask,n):return [1-2*((mask>>j)&1) for j in range(n)]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def mask(v):return sum((x<0)<<i for i,x in enumerate(v))
def norm_mask(v):return mask(v if v[0]>0 else [-x for x in v])
def tensor(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def had(s):return [[1-2*((i&j).bit_count()%2) for j in range(s)] for i in range(s)]
def orthogonal(a,n):
    assert all(len(v)==n and all(x in (-1,1) for x in v) for v in a)
    assert all(dot(x,y)==0 for x,y in combinations(a,2))


def main():
    base=json.loads((ROOT/'exchanges/partial24.json').read_text())['deadEnds'][0]
    a=[row(x,24) for x in base];orthogonal(a,24)
    small=[]
    for x in range(0,1<<24,2):
        bad=0;count=0
        for i,y in enumerate(base):
            if (x^y).bit_count()!=12:
                bad|=1<<i;count+=1
                if count>2:break
        else:small.append((x,bad))
    assert len(small)==56
    assert not any(bad==0 for x,bad in small)
    for i in range(16):
        assert [x for x,bad in small if bad&~(1<<i)==0]==[base[i]]
    special=[]
    for i,j in combinations(range(16),2):
        v=[x for x,bad in small if bad&~((1<<i)|(1<<j))==0]
        assert base[i] in v and base[j] in v
        extra=[x for x in v if x not in (base[i],base[j])]
        if not extra:continue
        assert len(extra)==2
        x,y=[row(z,24) for z in extra]
        px=[dot(a[k],x) for k in (i,j)]
        py=[dot(a[k],y) for k in (i,j)]
        assert all(abs(z)==12 for z in px+py)
        assert py==px or py==[-z for z in px]
        assert dot(x,y)==0
        if px[0]<0:x=[-z for z in x];px=[-z for z in px]
        if py!=px:y=[-z for z in y]
        assert [dot(a[k],y) for k in (i,j)]==px
        sigma=px[1]//12
        w=[(u+sigma*v)//2 for u,v in zip(a[i],a[j])]
        z=[(u-v)//2 for u,v in zip(x,y)]
        assert x==[u+v for u,v in zip(w,z)]
        assert y==[u-v for u,v in zip(w,z)]
        assert dot(w,z)==0 and dot(w,w)==dot(z,z)==12
        special.append((i,j,w,z))
    assert len(special)==20
    cert=json.loads((ROOT/'exchanges/augmentation24.json').read_text())
    q=[a[i] for i in range(16) if i not in cert['deleted']]+[row(x,24) for x in cert['newMasks']]
    full=[row(x,24) for x in cert['completedMasks']]
    orthogonal(q,24);orthogonal(full,24)
    tensorchecks=[]
    for s in (1,2,4,8):
        h=had(s);original=tensor(a,h);n=24*s
        deleted={i*s for i in cert['deleted']}
        augmented=[v for i,v in enumerate(original) if i not in deleted]
        augmented+=tensor([row(x,24) for x in cert['newMasks']],[h[0]])
        assert len(augmented)==16*s+1;orthogonal(augmented,n)
        repaired=tensor(q,h);complete=tensor(full,h)
        assert len(repaired)==17*s and len(complete)==24*s
        orthogonal(repaired,n);orthogonal(complete,n)
        tensorchecks.append({'factorOrder':s,'shape':[16*s,24*s],
                             'oneLiftedExchangeRows':len(augmented),
                             'allFibersRepairedRows':len(repaired),
                             'fullCompletionChecked':True})
    # Three representative tensor deletion cases, checked by a separate
    # exact nullspace enumeration rather than only the proof formulas.
    s=2;h=had(s);aa=tensor(a,h);i,j,w,z=special[0]
    cases=[('same_base',[(i,0),(i,1)]),
           ('different_fibers',[(i,0),(j,1)]),
           ('same_fiber',[(i,0),(j,0)])]
    candidatechecks=[]
    for name,deleted in cases:
        ds={ii*s+b for ii,b in deleted}
        kept=[v for ii,v in enumerate(aa) if ii not in ds]
        candidates,info=cube_kernel(kept,48)
        expected={norm_mask(aa[ii]) for ii in ds}
        if name=='same_fiber':
            for eps in product((-1,1),repeat=s):
                v=[w[ii]*h[0][b]+z[ii]*eps[b] for ii in range(24) for b in range(s)]
                expected.add(norm_mask(v))
        assert candidates==sorted(expected),(name,len(candidates),len(expected))
        assert not any(all((x^y).bit_count()==24 for x,y in combinations(v,2))
                       for v in combinations(candidates,3))
        candidatechecks.append({'case':name,'candidateLines':len(candidates),
                                'assignmentsTested':info['assignmentsTested']})
    report={'passed':True,'baseNormalizedCubeVectorsExhausted':1<<23,
            'singletonCaps':16,'pairCaps':120,'halfOverlapPairCaps':20,
            'baseMinimalExchangeCost':3,'uniformTensorExchangeCost':3,
            'uniformScope':'every Hadamard tensor factor, by the paper proof',
            'tensorChecks':tensorchecks,'independentTensorCandidateChecks':candidatechecks,
            'unboundedExchangeCostProved':False,'fullHadamardConjectureProved':False,
            'noveltyClaim':False}
    (HERE/'checks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
