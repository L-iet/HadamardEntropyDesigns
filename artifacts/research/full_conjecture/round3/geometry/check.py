"""Exact rational checks of tensor destabilization; standard library only."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent


def mm(a,b):return [[sum(x*y for x,y in zip(ar,bc)) for bc in zip(*b)] for ar in a]
def tr(a):return list(map(list,zip(*a)))
def identity(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def tensor(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def house(n):return [[F(2,n)-int(i==j) for j in range(n)] for i in range(n)]
def had4():return [[F(1-2*((i&j).bit_count()%2),2) for j in range(4)] for i in range(4)]


def basis(n,sym):
    if sym:
        for i in range(n):
            x=[[F(0) for j in range(n)] for k in range(n)];x[i][i]=F(1)
            yield ('diag',i),x,F(1)
    for i,j in combinations(range(n),2):
        x=[[F(0) for j in range(n)] for k in range(n)]
        x[i][j]=F(1);x[j][i]=F(1 if sym else -1)
        yield ('pair',i,j),x,F(1,2)  # normalization squared


def quantities(u,p):
    n=len(u[0])
    assert mm(u,tr(u))==identity(len(u))
    w=[[abs(x)**(p-2)*x for x in row] for row in u]
    m=mm(tr(u),w)
    assert m==tr(m)
    q=sum(abs(x)**p for row in u for x in row)
    r=sum(abs(x)**(p-2) for row in u for x in row)
    return m,q,r


def ts(u,m,p,x):
    ux=mm(u,x)
    t=sum(abs(u[i][j])**(p-2)*ux[i][j]**2 for i in range(len(u)) for j in range(len(u[0])))
    xtx=mm(tr(x),x)
    s=sum(m[i][j]*xtx[j][i] for i in range(len(m)) for j in range(len(m)))
    return t,s


def certify(u,p,name):
    n=len(u[0]);m,q,r=quantities(u,p)
    sym=[];skew=[]
    for sign,items in ((True,sym),(False,skew)):
        for label,x,weight in basis(n,sign):
            t,s=ts(u,m,p,x)
            items.append((label,x,t,s,weight))
    assert sum(t*w for label,x,t,s,w in sym)==(r+q)/2
    assert sum(s*w for label,x,t,s,w in sym)==(n+1)*q/2
    assert sum(t*w for label,x,t,s,w in skew)==(r-q)/2
    assert sum(s*w for label,x,t,s,w in skew)==(n-1)*q/2
    flat=all(x*x==F(1,n) for row in u for x in row)
    if flat:
        assert r==n*q
        return {'name':name,'n':n,'p':p,'flat':True,'q':str(q)}
    assert q<=r<n*q
    y=min((v for v in skew if v[3]>0),key=lambda v:v[2]/v[3])
    z=min((v for v in sym if v[3]>0),key=lambda v:v[2]/v[3])
    alpha=y[2]/y[3];beta=z[2]/z[3]
    abound=(r-q)/((n-1)*q);bbound=(r+q)/((n+1)*q)
    assert 0<=alpha<=abound<1 and 0<=beta<=bbound<1
    k=1
    while (p-1)*alpha*beta**(k-1)>=1:k+=1
    curvature=p*y[3]*z[3]**(k-1)*((p-1)*alpha*beta**(k-1)-1)
    assert curvature<0
    # For small enough lifts, check the full lifted matrix independently.
    direct=None
    if n**k<=36:
        uk=u;xk=y[1]
        for j in range(k-1):uk=tensor(uk,u);xk=tensor(xk,z[1])
        mk,qk,rk=quantities(uk,p)
        assert qk==q**k
        tk,sk=ts(uk,mk,p,xk)
        direct=p*((p-1)*tk-sk)
        assert direct==curvature
    return {'name':name,'n':n,'p':p,'flat':False,'q':str(q),'r':str(r),
            'alpha':str(alpha),'beta':str(beta),'alphaBound':str(abound),'betaBound':str(bbound),
            'tensorFactors':k,'liftedOrder':n**k,'curvature':str(curvature),
            'Y':y[0],'Z':z[0],'directLiftChecked':direct is not None}


def main():
    cases=[]
    for n in (2,3,4,5,6,7):
        for p in (3,4,5,6,8):cases.append(certify(house(n),p,'Householder'))
    # Test a matrix with many zeros, independently of the Householder case.
    u=identity(6)
    b=had4()
    for i in range(4):
        for j in range(4):u[i][j]=b[i][j]
    for p in (3,4,6):cases.append(certify(u,p,'Hadamard4 direct-sum I2'))
    for p in (3,4,6):
        cases.append(certify(had4()[:2],p,'flat row frame2x4'))
        cases.append(certify([row+[F(0),F(0)] for row in had4()[:2]],p,'stationary row frame2x6'))
    a=house(5);m,q,r=quantities(a,4)
    y=[[F(0) for j in range(5)] for i in range(5)]
    for i,j,v in ((0,1,1),(1,2,1),(0,2,-1)):y[i][j]=F(v);y[j][i]=F(-v)
    z=[[F(0) for j in range(5)] for i in range(5)]
    for i,j,v in ((0,1,1),(1,2,-1),(2,3,1),(3,0,-1)):z[i][j]=z[j][i]=F(v)
    u2=tensor(a,a);x=tensor(y,z);m2,q2,r2=quantities(u2,4)
    t,s=ts(u2,m2,4,x)
    assert 4*(3*t-s)==F(-192,625)
    out={'passed':True,'exactCases':len(cases),'cases':cases,
         'twoCopyExample':{'baseOrder':5,'liftedOrder':25,'curvature':'-192/625','directChecked':True},
         'generalRealExponentsProvedIn':'tensor_stability.tex',
         'numericScope':'integer exponents checked exactly; all real p>2 covered by paper proof',
         'hadamardConjectureProved':False,'noveltyEstablished':False}
    (HERE/'checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('Passed',len(cases),'exact trace/ratio cases; direct two-copy curvature -192/625.')


if __name__=='__main__':main()
