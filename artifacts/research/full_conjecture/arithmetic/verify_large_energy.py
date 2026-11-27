"""Exact tests of a proved large-energy group-ring construction.

Standard library only; new project-authored code, Apache-2.0 as in ../LICENSE.
"""
from pathlib import Path
from math import isqrt
import json

HERE=Path(__file__).resolve().parent


def three_squares(n):
    assert n>0 and n%8==3
    for u in range(1,isqrt(n)+1,2):
        for v in range(1,isqrt(n-u*u)+1,2):
            r=n-u*u-v*v
            w=isqrt(r)
            if w*w==r:
                assert w%2
                return [u,v,w]
    raise AssertionError('Three-square representation not found')


def construct(m,t):
    assert m%2==1 and t%2==1 and 4*t>=m*m+3
    u,v,w=three_squares(4*t-m*m)
    if (u+v+w-m)%4:u=-u
    numerators=[-m+u+v+w,-m+u-v-w,-m-u+v-w,-m-u-v+w]
    assert all(a%4==0 for a in numerators)
    x=[a//4 for a in numerators]
    assert sum(x)==-m and sum(a*a for a in x)==t
    seqs=[[1+2*a]+[1]*(m-1) for a in x]
    check(m,t,seqs)
    return {'m':m,'t':t,'threeSquares':[u,v,w],'x':x,
            'constantCoefficients':[a[0] for a in seqs]}


def check(m,t,seqs):
    assert len(seqs)==4 and all(len(a)==m for a in seqs)
    assert all(v%2 for a in seqs for v in a)
    for s in range(m):
        actual=sum(a[j]*a[(j+s)%m] for a in seqs for j in range(m))
        assert actual==(4*t if s==0 else 0),(m,t,s,actual)


def four_squares(n):
    for a in range(isqrt(n)+1):
        for b in range(isqrt(n-a*a)+1):
            for c in range(isqrt(n-a*a-b*b)+1):
                d=isqrt(n-a*a-b*b-c*c)
                if a*a+b*b+c*c+d*d==n:return a,b,c,d
    raise AssertionError('Four-square representation not found')


def multiply(seqs,s):
    a,b,c,d=four_squares(s)
    mat=[[a,b,c,d],[-b,a,-d,c],[-c,d,a,-b],[-d,-c,b,a]]
    assert all(sum(mat[k][i]*mat[k][j] for k in range(4))==(s if i==j else 0)
               for i in range(4) for j in range(4))
    assert all(sum(row)%2 for row in mat)
    return [[sum(mat[i][k]*seqs[k][j] for k in range(4))
             for j in range(len(seqs[0]))] for i in range(4)]


def prime(n):
    return n>1 and all(n%d for d in range(2,isqrt(n)+1))


def skew_construct(p,t):
    assert prime(p) and p%4==3 and t%2 and t>=(p*p+6*p+21)//16
    squares={j*j%p for j in range(1,p)}
    legendre=[0]+[1 if j in squares else -1 for j in range(1,p)]
    assert all(legendre[(-j)%p]==-legendre[j] for j in range(p))
    for s in range(p):
        assert sum(legendre[j]*legendre[(j+s)%p] for j in range(p))==(p-1 if s==0 else -1)
    x=(3-p)//4
    abc=three_squares(4*t-3*p-4*x*x)
    seqs=[[a]+legendre[1:] for a in abc]+[[1+2*x]+[1]*(p-1)]
    check(p,t,seqs)
    return {'m':p,'t':t,'threshold':(p*p+6*p+21)//16,
            'abc':abc,'x':x,'constantCoefficients':[a[0] for a in seqs]}


def main():
    witnesses=[]
    for m in range(1,102,2):
        t0=(m*m+3)//4
        for delta in (0,2,4,10,50,200):witnesses.append(construct(m,t0+delta))
    mult=[]
    for m in (1,3,5,7,9,11):
        t=(m*m+3)//4
        w=construct(m,t)
        seqs=[[1+2*a]+[1]*(m-1) for a in w['x']]
        for s in range(1,102,2):
            check(m,s*t,multiply(seqs,s))
            mult.append({'m':m,'t':t,'oddMultiplier':s})
    skew=[]
    for p in range(3,200,4):
        if prime(p):
            for delta in (0,2,10,50):
                skew.append(skew_construct(p,(p*p+6*p+21)//16+delta))
    record={'passed':True,'generalTheorem':'odd m,t and 4t>=m^2+3 imply parity-constrained norm solvability',
            'generalProof':'large_energy.tex','allOrdersHadamardConjectureProved':False,
            'largeEnergyCasesChecked':len(witnesses),'oddMultiplierCasesChecked':len(mult),
            'skewCharacterCasesChecked':len(skew),
            'witnesses':witnesses,'multiplierCases':mult,'skewCharacterCases':skew}
    (HERE/'checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Passed',len(witnesses),'large-energy cases,',len(mult),
          'odd-multiplier cases and',len(skew),'skew-character cases.')


if __name__=='__main__':main()
