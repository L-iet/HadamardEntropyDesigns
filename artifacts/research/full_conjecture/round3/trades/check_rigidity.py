"""Exact arithmetic and positive-trade checks; no external dependencies."""
from itertools import combinations, product
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import json
from classify import solve, rank, dot

ROOT=Path(__file__).resolve().parent


def isprime(n):
    if n<2:return False
    if n%2==0:return n==2
    return all(n%d for d in range(3,isqrt(n)+1,2))


def smallest_prime(n):
    if n%2==0:return 2
    for d in range(3,isqrt(n)+1,2):
        if n%d==0:return d
    return n


def paley(p):
    assert isprime(p) and p%4==3
    def chi(x):
        x%=p
        return 0 if not x else (1 if pow(x,(p-1)//2,p)==1 else -1)
    h=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
    assert all(dot(a,b)==0 for a,b in combinations(h,2))
    return h


def degree_barrier(m):
    p=smallest_prime(m);r=1
    while all(k**k < p*p*4**(k-1) for k in range(1,r+1)):
        r+=1
    return r


def enumerate_span(rows):
    n=len(rows[0]);r=len(rows)
    columns=list(zip(*rows));anchors=[]
    for j,p in enumerate(columns):
        if rank([columns[i] for i in anchors]+[p])>len(anchors):anchors.append(j)
        if len(anchors)==r:break
    assert len(anchors)==r
    out=set()
    for bits in product((-1,1),repeat=r):
        c=solve([columns[i] for i in anchors],bits)
        if all(dot(c,p) in (-1,1) for p in columns):out.add(c)
    return out


def main():
    examples=[]
    for b in (3,7,13,19,31):
        primes=[p for p in range(3,b+1,2) if isprime(p)]
        P=prod(primes)
        c=next(c for c in range(1,9) if (1+c*P)%8==3)
        j=0
        while not isprime(1+(c+8*j)*P):j+=1
        q=1+(c+8*j)*P;n=q+1;m=n//4
        assert q%8==3 and m%2==1
        assert all(q%p==1 and m%p!=0 for p in primes)
        p=smallest_prime(m)
        assert p>b
        examples.append({'roughnessCutoff':b,'modulus':8*P,'prime':q,'order':n,
                         'oddPart':m,'leastPrimeFactor':p,
                         'minimumTradeVolumeAtLeastByDeterminantBound':degree_barrier(m),
                         'primalityMethod':'trial division through integer square root'})
    span_checks=[]
    for p,r in ((11,3),(19,5),(43,6),(211,8)):
        h=paley(p);n=p+1
        allowed=enumerate_span(h[:r])
        expected={tuple(Fraction(sign*int(i==j)) for i in range(r))
                  for j in range(r) for sign in (-1,1)}
        assert allowed==expected
        span_checks.append({'order':n,'rows':r,'signVectors':len(allowed),
                            'newSignVectorsUpToNegation':0})
    # Sharp degree-six trade in Paley order12.
    h=paley(11);inds=(0,1,2,3,5,8);k=6
    sums=[sum(h[i][j] for i in inds) for j in range(12)]
    assert all(x in (-6,0,6) for x in sums)
    changed=[row[:] for row in h]
    for i in inds:
        changed[i]=[s//3-x for s,x in zip(sums,h[i])]
    assert all(x in (-1,1) for row in changed for x in row)
    assert all(row[0]==1 for row in changed)
    assert all(dot(a,b)==0 for a,b in combinations(changed,2))
    before={tuple(row) for row in h};after={tuple(row) for row in changed}
    assert len(before-after)==len(after-before)==6
    six_trade={'order':12,'rowIndices':inds,'oldRows':h,'newRows':changed}
    # Universal half-row trade at four known orders.
    half=[]
    for p in (7,11,19,43):
        h=paley(p);n=p+1;k=n//2
        inds=[i for i in range(n) if h[i][1]==1]
        assert len(inds)==k
        sums=[sum(h[i][j] for i in inds) for j in range(n)]
        changed=[row[:] for row in h]
        for i in inds:
            changed[i]=[2*s//k-x for s,x in zip(sums,h[i])]
        assert all(x in (-1,1) for row in changed for x in row)
        assert all(row[0]==1 for row in changed)
        assert all(dot(a,b)==0 for a,b in combinations(changed,2))
        assert len({tuple(x) for x in h}-{tuple(x) for x in changed})==k
        half.append({'order':n,'tradeVolume':k})
    out={'passed':True,'roughPaleyOrders':examples,'sampleSpanChecks':span_checks,
         'sharpDegreeSixTrade':six_trade,
         'universalHalfRowTradeChecks':half,
         'scope':'finite checks supplement paper proofs; no full Hadamard proof or novelty claim'}
    (ROOT/'rigidity_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('All rigidity checks passed.')
    for x in examples:print({k:x[k] for k in ('roughnessCutoff','order','leastPrimeFactor','minimumTradeVolumeAtLeastByDeterminantBound')})


if __name__=='__main__':main()
