# SPDX-License-Identifier: Apache-2.0
"""Exact Fourier coverage and reweighting checks, standard library only."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json


def chi(a,z):return (-1)**((a&z).bit_count()%2)
def addset(a):return {x^y for x in a for y in a}
def rank(masks):
    pivots={}
    for mask in masks:
        while mask:
            p=mask.bit_length()-1
            if p in pivots:mask^=pivots[p]
            else:pivots[p]=mask;break
    return len(pivots)


def main():
    cover_cases=0;missing_cases=0
    for r in (2,3):
        size=1<<r
        for d in range(r,size):
            for b in combinations(range(1,size),d):
                if rank(b)!=r:continue
                sums=addset((0,)+b)
                if d+1>size//2:assert len(sums)==size
                cover_cases+=1
                for c in set(range(size))-sums:
                    for t in (F(-1),F(1,3),F(1)):
                        p=[(1+t*chi(c,z))/size for z in range(size)]
                        assert sum(p)==1 and min(p)>=0
                        fourier=[sum(p[z]*chi(a,z) for z in range(size)) for a in range(size)]
                        assert all(fourier[a]==0 for a in sums-{0})
                        collision=sum(w*w for w in p)
                        assert collision==(1+t*t)/size
                        assert collision==sum(w*w for w in fourier)/size
                        if abs(t)==1:assert sum(w>0 for w in p)==size//2
                        missing_cases+=1
    # Approximate-moment Parseval inequality on a fully covered nonuniform seed.
    b=(1,2,3,4);size=8;p=[F(1,4)]+[F(3,28)]*7
    assert len(addset((0,)+b))==size and sum(p)==1
    moments=[sum(p[z]*chi(c,z) for z in range(size)) for c in range(size)]
    eps=max(abs(moments[c]) for c in range(1,size))
    assert sum(w*w for w in p)<=F(1,size)+F(size-1,size)*eps*eps
    deficits=[]
    for target in range(12,257,4):
        if target&(target-1)==0:continue
        d=target-4;r=(d).bit_length();size=1<<r
        assert d+1>size//2 and size>=target+4 and size<2*target
        gap=F(1,target)-F(1,size)
        assert gap>F(2,target*target)>F(1,1024*target**4)
        deficits.append({'target':target,'bits':d,'seedAtoms':size,'collisionDeficit':str(gap)})
    record={'passed':True,'spanningMaskSets':cover_cases,'exactHyperplaneLaws':missing_cases,
            'nonPowerOfTwoTargets':deficits,'approximateParsevalCasePassed':True}
    Path(__file__).with_name('character_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Character checks passed:',cover_cases,'mask sets;',missing_cases,'hyperplane laws.')


if __name__=='__main__':main()
