"""Exact integral tangent Hessian for optional small-order investigations."""
from itertools import combinations


def tensor(a,b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def householder(n):
    return [[2-n*int(i==j) for j in range(n)] for i in range(n)]


def sylvester(n):
    return [[1-2*((i&j).bit_count()%2) for j in range(n)] for i in range(n)]


def hessian(v):
    n=len(v)
    m=[[sum(v[k][i]*v[k][j]**3 for k in range(n)) for j in range(n)] for i in range(n)]
    assert m==list(map(list,zip(*m)))
    basis=[]
    for a,b in combinations(range(n),2):
        entries=[(a,b,1),(b,a,-1)]
        vx=[[sum(v[i][k]*s for k,jj,s in entries if jj==j) for j in range(n)] for i in range(n)]
        basis.append((entries,vx))
    h=[]
    for x,vx in basis:
        row=[]
        for y,vy in basis:
            first=12*sum(v[i][j]**2*vx[i][j]*vy[i][j] for i in range(n) for j in range(n))
            second=4*sum(m[j][i]*sx*sy for i,k,sx in x for kk,j,sy in y if k==kk)
            row.append(first+second)
        h.append(row)
    assert h==list(map(list,zip(*h)))
    return h


if __name__=='__main__':
    h=hessian(householder(5))
    assert all(h[i][i]>0 for i in range(len(h)))
    print('Computed exact order-five tangent Hessian; see verify.py for the uniform positivity certificate.')
