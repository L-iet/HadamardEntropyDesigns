# SPDX-License-Identifier: Apache-2.0
"""Exact flat-POVM commutator and Walsh dilation certificates."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
root=Path(__file__).resolve().parent
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def comm(a,b):
    ab=mm(a,b);ba=mm(b,a)
    return [[x-y for x,y in zip(r,s)] for r,s in zip(ab,ba)]
rows=[(1,)+x for x in product((-1,1),repeat=3)];n=4;m=8
effects=[[[F(x*y,m) for y in row] for x in row] for row in rows]
assert all(sum(e[i][j] for e in effects)==(i==j) for i in range(n) for j in range(n))
actual=sum(sum(x*x for row in comm(a,b) for x in row) for a in effects for b in effects)
formula=sum(F(2*(sum(x*y for x,y in zip(a,b)))**2*(n*n-(sum(x*y for x,y in zip(a,b)))**2),m**4)
            for a in rows for b in rows)
assert actual==formula==F(3,4)
assert sum(sum(e[i][i]-mm(e,e)[i][i] for i in range(n)) for e in effects)==n-F(n*n,m)

# Exact compressed h16,k12 law with omitted spanning field basis.
s=4;h=1<<s;k=12;n=k*h;m=h*h;poly=0b10011
def multiply(a,b):
    out=0
    while b:
        if b&1:out^=a
        b>>=1;a<<=1
        if a&h:a^=poly
    return out
omitted={1,2,4,8};slopes=[t for t in range(h) if t not in omitted]
frequencies=[0]
for t in slopes:
    for alpha in range(1,h):
        beta=sum(((alpha&multiply(t,1<<j)).bit_count()%2)<<j for j in range(s))
        frequencies.append(alpha|(beta<<s))
for t in slopes:
    if not t:continue
    beta=sum((multiply(t,1<<j)&1)<<j for j in range(s))
    frequencies.append(beta<<s)
assert len(frequencies)==len(set(frequencies))==n
fourier=[sum((-1)**((seed&f).bit_count()) for seed in range(m)) for f in range(m)]
assert fourier==[m]+[0]*(m-1)
assert all(fourier[a^b]==m*(i==j) for i,a in enumerate(frequencies) for j,b in enumerate(frequencies))
masks=[sum(((seed&f).bit_count()%2)<<j for j,f in enumerate(frequencies)) for seed in range(m)]
assert len(set(masks))==m
s2=0;s4=0;maxopnumerator=0
for a,x in enumerate(masks):
    for b,y in enumerate(masks):
        dot=n-2*(x^y).bit_count();s2+=dot**2;s4+=dot**4
        assert (dot==0)==(a//h==b//h and a!=b)
        maxopnumerator=max(maxopnumerator,dot**2*(n*n-dot**2))
assert s2==n*m*m
lam=F(n,m);energy=2*(n*lam*lam-F(s4,m**4));maxop2=F(maxopnumerator,m**4)
assert 0<energy/n<=2*lam*lam*(1-lam)
assert maxop2<=lam**3*(1-lam)
out=dict(passed=True,smallPOVMExactCommutatorEnergy=str(actual),h=h,k=k,n=n,m=m,
         relativeCollision=str(lam),effectProjectivityDefect=str(lam*(1-lam)),
         normalizedCommutatorEnergy=str(energy/n),maximumPairOperatorCommutatorSquared=str(maxop2),
         flatWalshNaimarkDimension=m,relativeDilationOverhead=str(F(m,n)-1),
         exactHadamardMixtureTVDistance=str(1-F(1,k)),orthogonalityGraph='h disjoint K_h')
(root/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
