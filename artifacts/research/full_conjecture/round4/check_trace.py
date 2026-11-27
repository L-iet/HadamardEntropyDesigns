# SPDX-License-Identifier: Apache-2.0
"""Exact rational tangent-trace and tensor certificate checks (stdlib only)."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def tensor(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def moments(u, p):
    return sum(abs(x)**p for row in u for x in row), sum(abs(x)**(p-2) for row in u for x in row)


def curvature(u, p, a, b):
    return p*sum((p-1)*(abs(row[a])**(p-2)*row[b]**2
                            +abs(row[b])**(p-2)*row[a]**2)
                 -abs(row[a])**p-abs(row[b])**p for row in u)


def check(u, p):
    d,n=len(u),len(u[0])
    assert all(sum(u[i][j]*u[k][j] for j in range(n))==(i==k)
               for i in range(d) for k in range(d))
    q,r=moments(u,p)
    direct=sum(curvature(u,p,a,b) for a in range(n) for b in range(a+1,n))
    assert direct==p*((p-1)*r-(n+p-2)*q)
    assert r<=n*q
    if p==4:
        e=n*q/d
        variance=sum((x*x-F(1,n))**2 for row in u for x in row)
        assert variance==F(d,n)*(e-1)
    return {'rows':d,'columns':n,'p':p,'q':str(q),'r':str(r),'rotationTrace':str(direct)}


def main():
    results=[]
    for n in range(2,8):
        u=[[F(2,n)-(i==j) for j in range(n)] for i in range(n)]
        for d in sorted({1,n//2,n}):
            for p in (3,4,5,6):results.append(check(u[:d],p))
    # Zeros are included, not discarded as nonsmooth cases at p>2.
    u=[[F(i==j) for j in range(4)] for i in range(4)]
    for p in (3,4,6):results.append(check(u,p))
    tensor_cases=0
    for n in (2,3,4):
        u=[[F(2,n)-(i==j) for j in range(n)] for i in range(n)]
        for p in (3,4):
            v=tensor(u,u);q,r=moments(u,p)
            assert moments(v,p)==(q*q,r*r)
            check(v,p)
            c=[sum(abs(row[a])**p for row in u) for a in range(n)]
            cross=[[sum(abs(row[a])**(p-2)*row[b]**2 for row in u)
                    for b in range(n)] for a in range(n)]
            words=list(product(range(n),repeat=2))
            for a,aa in enumerate(words):
                for b in range(a+1,len(words)):
                    bb=words[b]
                    cert=p*((p-1)*(cross[aa[0]][bb[0]]*cross[aa[1]][bb[1]]
                                   +cross[bb[0]][aa[0]]*cross[bb[1]][aa[1]])
                            -c[aa[0]]*c[aa[1]]-c[bb[0]]*c[bb[1]])
                    assert cert==curvature(v,p,a,b)
            tensor_cases+=1
    # No floating-point test is used to determine activation.
    u=[[F(2,5)-(i==j) for j in range(5)] for i in range(5)]
    q,r=moments(u,4)
    k=1
    while 3*r**k-(5**k+2)*q**k>=0:k+=1
    assert k==8
    record={'passed':True,'baseCases':len(results),'directTensorCases':tensor_cases,
            'quarticA5TraceActivation':k,'cases':results,
            'scope':'Exact checks support the written proof; no general theorem is inferred from finite cases.'}
    Path(__file__).with_name('trace_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Trace checks passed:',len(results),'base cases,',tensor_cases,'direct tensor cases.')


if __name__=='__main__':main()
