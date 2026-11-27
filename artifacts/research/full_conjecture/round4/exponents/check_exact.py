# SPDX-License-Identifier: Apache-2.0
"""Exact rational checks; no external packages or downloaded source code."""
from fractions import Fraction as F
import json

def case(n, p, diag_weight):
    u = [[F(2,n)-(i==j) for j in range(n)] for i in range(n)]
    weight = [[diag_weight if i==j else F(1) for j in range(n)] for i in range(n)]
    m = [[sum(u[k][i]*weight[k][j]*u[k][j] for k in range(n))
          for j in range(n)] for i in range(n)]
    assert m == list(map(list,zip(*m)))
    assert all(sum(u[k][i]*u[k][j] for k in range(n)) == (i==j)
               for i in range(n) for j in range(n))
    q = sum(m[i][i] for i in range(n))
    r = sum(map(sum,weight))
    # M = a I + c J. Both eigenvalues checked without floating point.
    a,c = m[0][0]-m[0][1],m[0][1]
    assert all(m[i][j] == c+a*(i==j) for i in range(n) for j in range(n))
    assert a>0 and a+n*c>0
    def forms(entries):
        v = [[F(0) for _ in range(n)] for _ in range(n)]
        for i,j,x in entries: v[i][j]=x
        uv=[[sum(u[i][k]*v[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        t=sum(weight[i][j]*uv[i][j]**2 for i in range(n) for j in range(n))
        s=sum(m[i][j]*sum(v[k][i]*v[k][j] for k in range(n)) for i in range(n) for j in range(n))
        return t,s
    # Unnormalized off-diagonal generators have squared norm 2.
    sy=[forms([(i,j,F(1)),(j,i,F(1))]) for i in range(n) for j in range(i+1,n)]
    sk=[forms([(i,j,F(1)),(j,i,F(-1))]) for i in range(n) for j in range(i+1,n)]
    di=[forms([(i,i,F(1))]) for i in range(n)]
    assert sum(t for t,s in di)+sum(t/2 for t,s in sy)==(r+q)/2
    assert sum(s for t,s in di)+sum(s/2 for t,s in sy)==(n+1)*q/2
    assert sum(t/2 for t,s in sk)==(r-q)/2
    assert sum(s/2 for t,s in sk)==(n-1)*q/2
    alpha=max(t/s for t,s in sk)
    beta=max(t/s for t,s in sy+di)
    assert alpha>1 and beta>1 and r>n*q
    k=1
    while (p-1)*alpha*beta**(k-1)<=1: k+=1
    assert k<10000
    return dict(n=n,p=str(p),alpha=str(alpha),beta=str(beta),first_positive_factored_hessian_k=k,
                normalized_hessian_bracket=str((p-1)*alpha*beta**(k-1)-1))

if __name__=='__main__':
    # U=2J/n-I. At n=10 the magnitude ratio is 4, so p=3/2
    # weights share a common positive factor sqrt(5), leaving diag 1/2.
    # At n=18 ratio 8, p=4/3 leaves diag 1/4 after a common factor.
    print(json.dumps([case(10,F(3,2),F(1,2)),case(18,F(4,3),F(1,4))],indent=2))
