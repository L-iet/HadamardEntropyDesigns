# SPDX-License-Identifier: Apache-2.0
"""Independent exact anti-Hermitian tangent trace checks (standard library)."""
from fractions import Fraction as F

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a): return (a[0],-a[1])
def norm(a): return a[0]**2+a[1]**2
zero=(F(0),F(0))
def matmul(a,b):
    n=len(a)
    return [[sum_pair(mul(a[i][k],b[k][j]) for k in range(n)) for j in range(n)] for i in range(n)]
def sum_pair(xs):
    out=zero
    for x in xs: out=add(out,x)
    return out
def check(n,p,phased):
    u=[[(F(2,n)-(i==j),F(0)) for j in range(n)] for i in range(n)]
    if phased is True:
        for j in range(n): u[0][j]=mul((F(3,5),F(4,5)),u[0][j])
    elif phased=='mixed':
        reflection=[row[:] for row in u]
        for i in range(n):u[i][0]=mul(u[i][0],(F(3,5),F(4,5)))
        u=matmul(u,reflection)
        # This interior phase mixes real and imaginary amplitudes instead
        # of merely multiplying an entire output row by a phase.
    assert all(sum_pair(mul(conj(u[k][i]),u[k][j]) for k in range(n))
               ==(F(i==j),F(0)) for i in range(n) for j in range(n))
    # p4 weights |u|²; p1 real rational seed weights 1/|u|.
    weights=[[norm(z) if p==4 else 1/abs(z[0]) for z in row] for row in u]
    q=sum(weights[i][j]*norm(u[i][j]) for i in range(n) for j in range(n))
    r=sum(map(sum,weights))
    total=F(0)
    count=0
    for kind in ('diag','real','imag'):
        for a in range(n):
            for b in range(a if kind=='diag' else a+1,n):
                if kind=='diag' and b!=a: continue
                x=[[zero for _ in range(n)] for _ in range(n)]
                if kind=='diag': x[a][a]=(F(0),F(1))
                elif kind=='real': x[a][b]=(F(1),F(0)); x[b][a]=(F(-1),F(0))
                else: x[a][b]=(F(0),F(1)); x[b][a]=(F(0),F(1))
                v=matmul(u,x); acc=matmul(v,x)
                h=F(0)
                for i in range(n):
                    for j in range(n):
                        z=u[i][j]; w=weights[i][j]
                        radial=mul(conj(z),v[i][j])[0]
                        h+=p*w*norm(v[i][j])+p*(p-2)*w*radial**2/norm(z)
                        h+=p*w*mul(conj(z),acc[i][j])[0]
                total+=h if kind=='diag' else h/2
                count+=1
    assert count==n*n
    expected=F(p,2)*(p*r-(2*n+p-2)*q)
    assert total==expected,(total,expected)
    print(dict(n=n,p=p,complex_phases=phased,trace=str(total),rho=str(r/(n*q))))
    return q,r

if __name__=='__main__':
    check(3,4,True)
    check(3,4,'mixed')
    q,r=check(5,1,False)
    # At p1 this nonflat real seed is tensor-stable in O(n), but cannot
    # remain locally maximal in U(n): positive complex trace eventually.
    k=1
    while r**k-(2*5**k-1)*q**k<=0: k+=1
    print('p1 real Householder seed: first positive complex tensor trace k =',k)
