# SPDX-License-Identifier: Apache-2.0
"""Original exact phase-Hessian saddle certificates, no numerical eigensolver."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import lcm
import json

ROOT=Path(__file__).resolve().parent
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def gram(a):return [[dot(r,s) for s in a] for r in a]
def trans(a):return list(map(list,zip(*a)))
def matvec(a,v):return [dot(r,v) for r in a]
def quad(a,v):return dot(v,matvec(a,v))
def finite_step(h,y,old):
    n=len(h);scale=max(abs(x) for x in y)
    def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def conjugate(a):return(a[0],-a[1])
    def norm(a):return a[0]*a[0]+a[1]*a[1]
    steps=0
    while True:
        t=F(1,2**steps)
        a=[]
        for i in range(n):
            row=[]
            for j in range(n):
                x=t*F(y[i*n+j],2*scale)
                row.append((h[i][j]*(1-x*x)/(1+x*x),h[i][j]*2*x/(1+x*x)))
            a.append(row)
        assert all(norm(x)==1 for row in a for x in row)
        en=F(0)
        for i in range(n):
            for j in range(n):
                products=[mul(x,conjugate(z)) for x,z in zip(a[i],a[j])]
                g=(sum(x[0] for x in products)-n*int(i==j),sum(x[1] for x in products))
                en+=norm(g)
        if en<old:return {'dyadicStep':str(t),'energy':str(en),'strictlyDecreased':True}
        steps+=1
def null(a):
    a=[list(map(F,r)) for r in a];m=len(a);n=len(a[0]);piv=[];k=0
    for j in range(n):
        hit=next((i for i in range(k,m) if a[i][j]),None)
        if hit is None:continue
        a[k],a[hit]=a[hit],a[k];t=a[k][j];a[k]=[x/t for x in a[k]]
        for i in range(m):
            if i!=k:
                t=a[i][j];a[i]=[x-t*y for x,y in zip(a[i],a[k])]
        piv.append(j);k+=1
        if k==m:break
    free=next(j for j in range(n) if j not in piv)
    v=[F(0)]*n;v[free]=F(1)
    for i,j in enumerate(piv):v[j]=-a[i][free]
    scale=lcm(*(x.denominator for x in v))
    return [int(x*scale) for x in v]
def hessian(h):
    n=len(h);a=[[0]*(n*n) for _ in range(n*n)]
    for i,j in combinations(range(n),2):
        for c,d in combinations(range(n),2):
            cells=[(i*n+c,1),(j*n+d,1),(i*n+d,-1),(j*n+c,-1)]
            p=-4*h[i][c]*h[i][d]*h[j][c]*h[j][d]
            for x,s in cells:
                for y,t in cells:a[x][y]+=p*s*t
    return a
def certify(h,save=False):
    n=len(h);g=gram(h);a=hessian(h)
    ishad=g==[[n*int(i==j) for j in range(n)] for i in range(n)]
    bound=max(sum(abs(x) for x in row) for row in a)
    chosen=None
    for orientation in ('columns','rows'):
        for c,d in combinations(range(n),2):
            v=[0]*(n*n)
            for i in range(n):
                if orientation=='columns':
                    v[i*n+c]=v[i*n+d]=h[i][c]*h[i][d]
                else:v[c*n+i]=v[d*n+i]=h[c][i]*h[d][i]
            assert quad(a,v)==0
            w=matvec(a,v)
            if any(w) and chosen is None:
                y=[(bound+1)*x-z for x,z in zip(v,w)]
                assert quad(a,y)<0
                chosen=(orientation,c,d,y)
    if ishad:
        assert chosen is None
        return {'hadamard':True}
    if chosen is None:
        u=null(trans(h));v=null(h)
        y=[h[i][j]*u[i]*v[j] for i in range(n) for j in range(n)]
        assert quad(a,y)<0
        chosen=('kernel',None,None,y)
    y=chosen[-1];value=quad(a,y)
    record={'n':n,'gramEnergy':sum((g[i][j]-n*int(i==j))**2 for i in range(n) for j in range(n)),
            'method':chosen[0],'curvature':value,'negative':value<0}
    if save:record.update(matrix=h,integerPhaseDirection=y,
                          exactRationalEscape=finite_step(h,y,record['gramEnergy']))
    return record

allfour=[]
for mask in range(512):
    h=[[1]*4 for _ in range(4)]
    for i in range(1,4):
        for j in range(1,4):h[i][j]=1-2*((mask>>((i-1)*3+j-1))&1)
    allfour.append(certify(h))
assert sum(r.get('hadamard',False) for r in allfour)==6
trap=json.loads((ROOT.parents[1]/'round14/spectral/trap8.json').read_text())['H']
h2=[[1,1],[1,-1]]
lift=[[x*y for x in ar for y in br] for ar in trap for br in h2]
cases=[certify(trap,True),certify(lift,True),certify([[1]*4 for _ in range(4)],True),
       certify([[1,1,1,1],[1,-1,1,-1]]*2,True)]
assert any(r['method']=='kernel' for r in cases)
(ROOT/'checks.json').write_text(json.dumps({'passed':True,'arithmetic':'integers and rational nullspaces',
    'normalizedOrderFour':512,'orderFourHadamard':6,'orderFourStrictSaddles':506,'cases':cases},indent=2)+'\n',encoding='utf-8')
print('Exact phase-saddle certificates passed: 506 normalized order-four saddles and four larger/singular cases.')
