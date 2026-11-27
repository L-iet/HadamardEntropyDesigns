"""Exact certificates for moment-semigroup progress; standard library only."""
from collections import Counter
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent


def moments(c,d):
    return ([sum(c.values())]
            +[sum(v for x,v in c.items() if (x>>i)&1) for i in range(d)]
            +[sum(v for x,v in c.items() if ((x>>i)&1) and ((x>>j)&1))
              for i,j in combinations(range(d),2)])


def assert_oa(c,d):
    n=sum(c.values())
    assert all(isinstance(v,int) and v>=0 for v in c.values())
    assert n>0 and n%4==0
    assert moments(c,d)==[n]+[n//2]*d+[n//4]*comb(d,2)


def canonical(n,d):
    c={0:n*(d*d-5*d+8)//8}
    c.update({1<<i:n*(3-d)//4 for i in range(d)})
    c.update({(1<<i)|(1<<j):n//4 for i,j in combinations(range(d),2)})
    return Counter(c)


def shells(d):
    s=d//2
    n=2*comb(2*s,s)
    catalan=comb(2*s,s)//(s+1)
    allowed=[s+1] if d%2 else [s,s+1]
    weights={0:catalan,**{k:1 for k in allowed}}
    assert sum(v*comb(d,k) for k,v in weights.items())==n
    assert sum(v*comb(d-1,k-1) for k,v in weights.items() if k>=1)==n//2
    assert sum(v*comb(d-2,k-2) for k,v in weights.items() if k>=2)==n//4
    if d<=11:
        c={x:weights.get(x.bit_count(),0) for x in range(1<<d)}
        assert_oa(c,d)
    low=min(k for k in range(d+1) if (2*k-d)**2<=d)
    return {'d':d,'runs':n,'shellMultiplicities':weights,
            'maximumWeight':max(allowed),'sharpWeightLowerBound':(d+2)//2,
            'permutationSymmetryRunLowerBound':comb(d,low),
            'centralWindowLowerIndex':low}


def cube_moves(d):
    allbits=(1<<d)-1
    for t in range(1<<d):
        if t.bit_count()<3:continue
        outside=allbits^t
        base=outside
        while True:
            plus=[];minus=[]
            u=t
            while True:
                (plus if u.bit_count()%2 else minus).append(base|u)
                if u==0:break
                u=(u-1)&t
            yield plus,minus
            if base==0:break
            base=(base-1)&outside


def isolated_trade():
    n=8;d=7
    h=[[1-2*((a&b).bit_count()%2) for b in range(n)] for a in range(n)]
    changed=[r[:] for r in h]
    for i in range(4):
        changed[i]=[sum(h[j][b] for j in range(4))//2-h[i][b] for b in range(n)]
    def masks(a):return [sum(int(x==-1)<<j for j,x in enumerate(r[1:])) for r in a]
    c=Counter(masks(h));cp=Counter(masks(changed))
    assert_oa(c,d);assert_oa(cp,d);assert c!=cp
    assert all(sum(x*y for x,y in zip(a,b))==0 for a,b in combinations(changed,2))
    count=0
    for plus,minus in cube_moves(d):
        for state in (c,cp):
            assert not all(state[x]>=1 for x in minus)
            assert not all(state[x]>=1 for x in plus)
        count+=1
    removed=list((c-cp).elements());added=list((cp-c).elements())
    assert len(removed)==len(added)==4
    assert min((x^y).bit_count() for x,y in combinations(removed,2))==4
    return {'d':d,'n':n,'oldPatternCounts':dict(c),'newPatternCounts':dict(cp),
            'removedMasks':removed,'addedMasks':added,
            'translatedCoordinateSubcubesTested':count,
            'legalCoordinateCubeMovesAtEitherEndpoint':0,
            'tradeDegree':4}


def triple_conversions():
    out=[]
    for d in (4,5):
        for ell in range(1,10):
            feasible=(ell>=2) if d==4 else ell%3==0
            if not feasible:
                out.append({'d':d,'L':ell,'feasibleByTheorem':False});continue
            c=canonical(4*ell,d)
            t=ell//2 if d==4 else ell//3
            for triple in combinations(range(d),3):
                # +odd parity vertices and -even parity vertices.
                bits=sum(1<<j for j in triple)
                sub=bits
                while True:
                    c[sub]+=t*(1 if sub.bit_count()%2 else -1)
                    if sub==0:break
                    sub=(sub-1)&bits
            assert_oa(c,d)
            out.append({'d':d,'L':ell,'feasibleByTheorem':True,
                        'commonTripleMoveMultiplicity':t,'witness':dict(c)})
    return out


def conductor(d):
    a=4
    while a<d+1:a*=2
    q=3;exp=1
    while True:
        b=q+1 if exp%2 else 2*(q+1)
        if b>=d+1:break
        q*=3;exp+=1
    A=a//4;B=b//4
    assert a%4==b%4==0 and gcd(A,B)==1
    threshold=4*(A-1)*(B-1)
    assert threshold<3*(d+1)**2
    # Check first hundred admissible sizes beyond the proven threshold.
    witnesses=[]
    for n in range(max(4,threshold),max(4,threshold)+400,4):
        m=n//4
        u=next(u for u in range(B) if (m-u*A)%B==0)
        v=(m-u*A)//B
        assert v>=0 and u*a+v*b==n
        if len(witnesses)<3:witnesses.append({'n':n,'sylvesterBlocks':u,'paleyBlocks':v})
    return {'d':d,'sylvesterOrder':a,'paleyOrder':b,'paleyPrimePower':q,
            'paleyType':1 if exp%2 else 2,'centralRayConductorUpperBound':threshold,
            'firstDecompositions':witnesses}


def main():
    report={'status':'elementary proven restrictions and constructions; no Hadamard proof',
            'shellConstructions':[shells(d) for d in range(2,41)],
            'cubeIsolationCertificate':isolated_trade(),
            'tripleConversionCertificates':triple_conversions(),
            'centralRayConductorBounds':[conductor(d) for d in (3,7,11,19,31,63,127,999)],
            'importantScope':'anchored move-order restriction does not exclude translated low-dimensional moves',
            'passed':True}
    (ROOT/'certificates.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('All checks passed.')
    print('Coordinate cube faces tested:',report['cubeIsolationCertificate']['translatedCoordinateSubcubesTested'])
    print('Non-cube four-for-four trade:',report['cubeIsolationCertificate']['removedMasks'],
          '->',report['cubeIsolationCertificate']['addedMasks'])
    print('Run count bounds and shell constructions verified through d=40.')


if __name__=='__main__':main()
