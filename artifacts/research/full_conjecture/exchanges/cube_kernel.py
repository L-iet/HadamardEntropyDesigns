"""Exact cube intersections via free coordinates; standard library only.

Rational elimination occurs once. The exponentially many assignments are
tested using integer dot products, so no floating-point tolerance is used.
"""
from fractions import Fraction
from itertools import product
from math import lcm


def rref_integer_constraints(rows,n):
    a=[[Fraction(x) for x in row] for row in rows]
    pivots=[];k=0
    for col in range(n):
        pos=next((i for i in range(k,len(a)) if a[i][col]),None)
        if pos is None:continue
        a[k],a[pos]=a[pos],a[k]
        v=a[k][col];a[k]=[x/v for x in a[k]]
        for i in range(len(a)):
            if i!=k and a[i][col]:
                v=a[i][col];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        pivots.append(col);k+=1
        if k==len(a):break
    free=[j for j in range(n) if j not in pivots]
    constraints=[]
    for i,pivot in enumerate(pivots):
        den=lcm(*(a[i][j].denominator for j in free)) if free else 1
        coeff=[int(-a[i][j]*den) for j in free]
        constraints.append((pivot,den,coeff))
    return free,constraints


def cube_kernel(rows,n):
    """Return sign masks up to negation, normalized at coordinate zero."""
    free,eqs=rref_integer_constraints(rows,n)
    if not free:return [],{'freeCoordinates':free,'constraints':eqs,'assignmentsTested':0}
    # Fix the first FREE coordinate positive, then normalize returned rows
    # at actual coordinate zero. Exactly one vector from each antipodal
    # pair is visited, even when coordinate zero is a pivot.
    masks=[]
    for tail in product((-1,1),repeat=len(free)-1):
        values=(1,)+tail
        v=[0]*n
        for j,x in zip(free,values):v[j]=x
        for pivot,den,co in eqs:
            x=sum(c*y for c,y in zip(co,values))
            if x not in (-den,den):break
            v[pivot]=x//den
        else:
            if v[0]<0:v=[-x for x in v]
            masks.append(sum((x<0)<<j for j,x in enumerate(v)))
    assert len(masks)==len(set(masks))
    return sorted(masks),{'freeCoordinates':free,'constraints':eqs,
                          'assignmentsTested':1<<(len(free)-1)}


def row(mask,n):return [1-2*((mask>>j)&1) for j in range(n)]


def clique(pool,target,n):
    if target==0:return []
    if len(pool)<target:return None
    for i,a in enumerate(pool):
        possible=[b for b in pool[i+1:] if (a^b).bit_count()==n//2]
        result=clique(possible,target-1,n)
        if result is not None:return [a]+result
    return None
