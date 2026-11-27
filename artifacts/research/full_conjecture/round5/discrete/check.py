"""Exact, standard-library checks of collision rounding and modular nonlifting."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import json

def dot(x,y): return sum(a*b for a,b in zip(x,y))
def walsh(n): return [tuple(1-2*((i&j).bit_count()%2) for j in range(n)) for i in range(n)]
def cube(n): return [(1,)+x for x in product((-1,1),repeat=n-1)]
def quantities(w):
    rows=list(w); n=len(rows[0]); m=[[sum(w[x]*x[i]*x[j] for x in rows) for j in range(n)] for i in range(n)]
    c=sum(v*v for v in w.values());e=sum((m[i][j]-int(i==j))**2 for i in range(n) for j in range(n))
    energy=sum(w[x]*w[y]*dot(x,y)**2 for x in rows for y in rows)
    edges=sum(w[x]*w[y] for x in rows for y in rows if dot(x,y)==0)
    assert energy==n+e and energy>=n*n*c+4*(1-c-edges)
    return n,c,e,edges

def merge(w):
    w=dict(w);initial=sum(w[x]*w[y] for x in w for y in w if dot(x,y)==0)
    while True:
        pair=next(((x,y) for x,y in combinations(w,2) if dot(x,y)!=0),None)
        if pair is None: break
        x,y=pair
        dx=sum(w[z] for z in w if dot(x,z)==0);dy=sum(w[z] for z in w if dot(y,z)==0)
        if dx<dy:x,y=y,x
        w[x]+=w.pop(y)
    final=sum(w[x]*w[y] for x in w for y in w if dot(x,y)==0)
    assert final>=initial and all(dot(x,y)==0 for x,y in combinations(w,2))
    return w

results=[]
for n in [4,8]:
    rows=cube(n);eps=F(1,10000);w={x:eps/len(rows) for x in rows}
    for x in walsh(n):w[x]+=(1-eps)/n
    n,c,e,edges=quantities(w)
    assert e==0 and (n*n-4)*c>n- F(4,n-1)
    cl=merge(w);assert len(cl)==n
    results.append(dict(n=n,collision=str(c),error=str(e),extractedClique=len(cl)))
    # Also test the genuinely approximate-moment certificate.
    h=walsh(n);w[h[0]]+=eps;w[h[1]]-=eps
    n,c,e,edges=quantities(w)
    assert e>0 and (n*n-4)*c>n+e-F(4,n-1)
    cl=merge(w);assert len(cl)==n
    results.append(dict(n=n,collision=str(c),error=str(e),extractedClique=len(cl)))
# Sharp five-bit example from six columns of the Sylvester order-eight matrix.
rows=[x[:6] for x in walsh(8)];assert len(set(rows))==8
w={x:F(1,8) for x in rows};n,c,e,edges=quantities(w)
assert n==6 and c==F(1,8) and e==0 and edges==F(1,2)
assert all(abs(dot(x,y)) in (0,2) for x,y in combinations(rows,2))
# Verify the graph obstruction on the entire five-bit cube, not only the example.
rows=cube(6)
assert not any(dot(x,y)==dot(x,z)==dot(y,z)==0 for x,y,z in combinations(rows,3))
# Atom bound can be sharp while collision bound is not: exchangeable five-bit measure.
rows=cube(6);w={x:F(1,12) for x in rows if sum(x[1:])==-1};w[(1,)*6]=F(1,6)
n,c,e,edges=quantities(w);assert e==0 and c==F(7,72)<F(1,8) and max(w.values())==F(1,6)
mods=[]
for p in [3,5,7]:
    for t in [1,2]:
        n=4+4*p*t;b=[[1-2*int(i==j) for j in range(n)] for i in range(n)]
        assert n%4==0 and n%p!=0
        assert all((dot(b[i],b[j])-n*int(i==j))%p==0 for i in range(n) for j in range(n))
        assert dot(b[0],b[1])==n-4!=0
        assert (n-4)%(p*p)!=0  # chosen t are prime-to-p
        mods.append(dict(n=n,prime=p,offDiagonal=n-4,modPrimeSquaredFails=True))
# Reconstruct the two missing columns solely from the retained rows.
def complete_two(v):
    m=len(v);n=len(v[0]);assert m==n+2 and n%4==2
    cols=list(zip(*v));assert all(dot(x,y)==m*int(i==j) for i,x in enumerate(cols) for j,y in enumerate(cols))
    parity=lambda x: sum(a<0 for a in x)%2
    groups=[[i for i,x in enumerate(v) if parity(x)==b] for b in [0,1]]
    assert all(groups) and all(len(g)==m//2 for g in groups)
    added=[None]*m
    for b,g in enumerate(groups):
        base=g[0]
        for i in g:
            residual=m*int(i==base)-dot(v[i],v[base])
            assert residual in (-2,2)
            sign=residual//2
            added[i]=(sign,sign if b==0 else -sign)
    h=[tuple(x)+added[i] for i,x in enumerate(v)]
    assert all(dot(x,y)==m*int(i==j) for i,x in enumerate(h) for j,y in enumerate(h))
    return h
reconstructions=[]
for m in [8,16,32]:
    h=walsh(m);pairs=list(combinations(range(1,m),2))
    if m==32:pairs=pairs[:12]
    for a,b in pairs:
        v=[tuple(x[j] for j in range(m) if j not in (a,b)) for x in h]
        completed=complete_two(v)
        w={x:F(1,m) for x in v};n,c,e,edges=quantities(w)
        assert e==0 and c==F(1,n+2) and edges==F(1,2)
    reconstructions.append(dict(order=m,deletedColumnPairs=len(pairs),completed=True))
out={'passed':True,'roundingExamples':results,'sharpFiveBitCollision':'1/8','fiveBitGraphTriangleFree':True,'atomBoundSharpExampleCollision':'7/72','modularExamples':mods,'equalityReconstructions':reconstructions}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
