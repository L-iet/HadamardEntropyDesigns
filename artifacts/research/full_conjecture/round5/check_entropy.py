# SPDX-License-Identifier: Apache-2.0
"""Exact checks for entropy-window algebra and saturated-atom constructions."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from pathlib import Path
import json


def main():
    cases=[]
    for n in (4,6,8,10,12):
        d=n-1;count=comb(d,(n-2)//2)
        atoms=[((1,)*d,F(1,n))]
        for positive in combinations(range(d),(n-2)//2):
            pos=set(positive)
            atoms.append((tuple(1 if i in pos else -1 for i in range(d)),F(n-1,n*count)))
        assert sum(w for _,w in atoms)==1
        assert max(w for _,w in atoms)==F(1,n)
        assert all(sum(w*x[i] for x,w in atoms)==0 for i in range(d))
        assert all(sum(w*x[i]*x[j] for x,w in atoms)==0 for i in range(d) for j in range(i))
        c=sum(w*w for _,w in atoms)
        assert c==F(1,n*n)+F((n-1)**2,n*n*count)
        cases.append({'n':n,'supportSize':len(atoms),'largestAtom':str(F(1,n)),'collision':str(c)})
    for n in range(4,101,2):
        basic=(n-F(4,n-1))/F(n*n-4)
        assert basic==F(1,n)-F(4,n*(n-1)*(n*n-4))
        rank_one=(n-F(4,n-2))/F(n*n-4)
        assert rank_one==F(1,n)-F(8,n*(n-2)*(n*n-4))
        assert 0<rank_one<basic
        if n%4==0 and n>=12:
            enhanced=(n-F(4,n-8))/F(n*n-4)
            assert enhanced==F(1,n)-F(32,n*(n-8)*(n*n-4))
            assert 0<enhanced<basic<F(1,n)
    k=[[1,1,1,1],[1,-1,1,-1],[1,1,-1,-1],[1,-1,-1,1]]
    x=[[z for z in row for _ in range(3)] for row in k]
    assert all(sum(a*b for a,b in zip(x[i],x[j]))==12*(i==j) for i in range(4) for j in range(4))
    # Every possible block-sum vector has odd components and fails Kb=0.
    from itertools import product
    assert all(any(sum(k[i][j]*b[j] for j in range(4)) for i in range(4))
               for b in product((-3,-1,1,3),repeat=4))
    record={'passed':True,'saturatedAtomCases':cases,'thresholdAlgebraCases':49,
            'unextendible4by12BlockSumCases':256,
            'externalInput':'Seven-row completion theorem is cited, not independently reverified.'}
    Path(__file__).with_name('entropy_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Entropy and completion algebra checks passed.')


if __name__=='__main__':main()
