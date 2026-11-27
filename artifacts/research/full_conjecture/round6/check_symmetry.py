# SPDX-License-Identifier: Apache-2.0
"""Exact slice-moment and collision checks; Python standard library only."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from pathlib import Path
import json


def main():
    maxima=[];vertices=0
    for d in range(2,25):
        best=F(0);best_atoms=None
        for ks in combinations(range(d+1),3):
            ss=[2*k-d for k in ks]
            weights=[]
            for i in range(3):
                j,k=[t for t in range(3) if t!=i]
                weights.append(F(d+ss[j]*ss[k],(ss[i]-ss[j])*(ss[i]-ss[k])))
            if min(weights)<0:continue
            assert sum(weights)==1
            assert sum(w*s for w,s in zip(weights,ss))==0
            assert sum(w*s*s for w,s in zip(weights,ss))==d
            c=sum(w*w/comb(d,k) for w,k in zip(weights,ks));vertices+=1
            if c>best:best=c;best_atoms=[(k,str(w)) for k,w in zip(ks,weights)]
        n=4*((d+4)//4)
        assert best<=F(1,n)
        if d>=5:assert best<F(1,n)
        if d>=7:
            bound=F(1,d*d)+F(d,(d-2)**4)+F(2,d*(d-1))
            assert best<=bound<F(4,d*d)<F(1,d+4)
        maxima.append({'bits':d,'maximumSymmetricCollision':str(best),'sliceMasses':best_atoms})
    for d in range(7,201):
        assert F(1,d*d)+F(d,(d-2)**4)+F(2,d*(d-1))<F(4,d*d)
    # Exact verification of the binomial-mode estimate used in the entropy proof.
    modes=0
    for d in range(2,65):
        for k in range(d+1):
            mass=comb(d,k)*F(k,d)**k*F(d-k,d)**(d-k)
            assert mass>=F(1,d+1);modes+=1
    record={'passed':True,'exactSymmetricMaxima':maxima,'feasibleThreeSliceBases':vertices,
            'binomialModeCases':modes,
            'scope':'Finite exact checks support the analytic theorems; entropy series inequality is proved in the text.'}
    Path(__file__).with_name('symmetry_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Coordinate-symmetry checks passed:',vertices,'feasible slice bases;',modes,'mode inequalities.')


if __name__=='__main__':main()
