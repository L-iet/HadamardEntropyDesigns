# SPDX-License-Identifier: Apache-2.0
"""Exact checks of exchangeable mixtures; no external packages."""
from fractions import Fraction as F
from itertools import permutations, product
from collections import defaultdict

def moments(n, ensemble):
    d=n*n
    rho1=defaultdict(F); rho2=defaultdict(F)
    count=0
    for u in ensemble:
        count+=1
        assert all(sum(u[i*n+k]*u[j*n+k] for k in range(n))==(i==j)
                   for i in range(n) for j in range(n))
        nz=[(a,x) for a,x in enumerate(u) if x]
        for a,x in nz:
            for b,y in nz:
                rho1[a,b]+=x*y/n
                for c,z in nz:
                    for e,w in nz: rho2[a,c,b,e]+=x*y*z*w/(n*n)
    rho1={k:v/count for k,v in rho1.items()}
    rho2={k:v/count for k,v in rho2.items()}
    def entry(a,b,c,e):return rho2.get((a,b,c,e),F(0))
    swap=sum(entry(a,b,b,a) for a in range(d) for b in range(d))
    rowswap=F(0)
    for a in range(d):
        i,j=divmod(a,n)
        for b in range(d):
            k,l=divmod(b,n)
            rowswap+=entry(a,b,k*n+j,i*n+l)
    coincidence=sum(entry(a,a,a,a) for a in range(d))
    assert swap==1 and rowswap==F(1,n)
    print(dict(n=n,ensemble_size=count,full_swap=str(swap),row_swap=str(rowswap),coincidence=str(coincidence)))
    return rho1,coincidence

def signed_perms(n):
    for perm in permutations(range(n)):
        for signs in product((-1,1),repeat=n):
            yield [F(signs[i] if perm[i]==j else 0) for i in range(n) for j in range(n)]

if __name__=='__main__':
    n=3
    rho,c=moments(n,signed_perms(n))
    assert all(rho.get((a,b),F(0))==(F(1,n*n) if a==b else 0)
               for a in range(n*n) for b in range(n*n))
    assert c==F(1,n)>F(1,n*n)
    # Sylvester H4 / 2: exact genuine flat orthogonal comparison.
    u=[F(1 if (i&j).bit_count()%2==0 else -1,2) for i in range(4) for j in range(4)]
    _,c=moments(4,[u])
    assert c==F(1,16)
    print('All exact checks passed.')
