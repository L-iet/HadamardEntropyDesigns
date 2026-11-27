# SPDX-License-Identifier: Apache-2.0
"""Exact binary-rank, moment and support-overlap benchmark checks."""
from fractions import Fraction as F
from pathlib import Path
import json


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def rank(rows):
    pivots={}
    for value in rows:
        while value:
            p=value.bit_length()-1
            if p in pivots:value^=pivots[p]
            else:pivots[p]=value;break
    return len(pivots)
def walsh(values):
    values=list(values);w=1
    while w<len(values):
        for start in range(0,len(values),2*w):
            for i in range(start,start+w):
                a,b=values[i],values[i+w];values[i],values[i+w]=a+b,a-b
        w*=2
    return values


def paley_two(q):
    m=q+1;residues={x*x%q for x in range(1,q)}
    chi=lambda x:0 if x%q==0 else (1 if x%q in residues else -1)
    c=[[0 if i==j else (1 if i==0 or j==0 else chi(i-j)) for j in range(m)] for i in range(m)]
    assert all(dot(x,y)==q*(i==j) for i,x in enumerate(c) for j,y in enumerate(c))
    h=[[c[i][j]+(i==j) for j in range(m)]+[c[i][j]-(i==j) for j in range(m)] for i in range(m)]
    h+=[[c[i][j]-(i==j) for j in range(m)]+[-c[i][j]-(i==j) for j in range(m)] for i in range(m)]
    first=h[0]
    h=[[x*first[j] for j,x in enumerate(row)] for row in h]
    h=[[x*row[0] for x in row] for row in h]
    n=2*m
    assert all(dot(x,y)==n*(i==j) for i,x in enumerate(h) for j,y in enumerate(h))
    return h


def main():
    cases=[]
    for q in (5,13,29,61):
        h=paley_two(q);n=len(h);d=n-4;r=(n-1).bit_length();size=1<<r
        assert n%8==4 and d>=size//2 and size==n+4
        code=[sum(((z&a).bit_count()%2)<<i for i,a in enumerate(range(1,d+1))) for z in range(size)]
        assert len(set(code))==size and rank(code)==r
        p=set(code[:n])
        target={sum((int(x<0)<<i) for i,x in enumerate(row[1:d+1])) for row in h}
        assert len(target)==n and rank(target)==d
        # Binary column Gram I+J is checked as integer parity.
        cols=[sum(((row>>i)&1)<<j for j,row in enumerate(target)) for i in range(d)]
        assert all(((a&b).bit_count()%2)==(i!=j) for i,a in enumerate(cols) for j,b in enumerate(cols))
        overlap=len(p&target);assert overlap<=r+4
        fourier=walsh([int(z<n) for z in range(size)])
        masks=set(range(1,d+1))|{a^b for a in range(1,d+1) for b in range(a+1,d+1)}
        error=max(F(abs(fourier[a]),n) for a in masks)
        assert error<=F(size-n,n)==F(4,n)
        cases.append({'order':n,'seedBits':r,'candidateBinaryRank':r,'targetBinaryRank':d,
                      'maximumMomentError':str(error),'paleySupportOverlap':overlap,
                      'TVtoPaleyTarget':str(1-F(overlap,n)),
                      'TVtoAnyMinimalTargetLowerBound':str(1-F(r+4,n)),
                      'TVtoFullFeasibleWalshLaw':str(1-F(n,size))})
    record={'passed':True,'knownOrderBenchmarks':cases,
            'scope':'The infinite Paley subsequence uses the written density argument; finite checks do not prove density.'}
    Path(__file__).with_name('rank_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Rank and rounding checks passed at known orders12,28,60,124.')


if __name__=='__main__':main()
