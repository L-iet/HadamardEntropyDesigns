"""Reproducible exact checks; Python standard library, no external source code."""
from fractions import Fraction as F
from pathlib import Path
import json

def mm(a,b): return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def tr(a): return list(map(list,zip(*a)))
def kron(a,b): return [[x*y for x in r for y in s] for r in a for s in b]
def norm(a): return sum(x*x for r in a for x in r)
def ts(u,m,x,p):
    v=mm(u,x); xx=mm(tr(x),x)
    return (sum(abs(u[i][j])**(p-2)*v[i][j]**2 for i in range(len(u)) for j in range(len(u))),sum(m[i][j]*xx[j][i] for i in range(len(u)) for j in range(len(u))))
a=[[F(2,5)-int(i==j) for j in range(5)] for i in range(5)]
y=[[F(0) for j in range(5)] for i in range(5)]
z=[[F(0) for j in range(5)] for i in range(5)]
for i,j in [(0,1),(1,2),(2,0)]: y[i][j]=1;y[j][i]=-1
for i,j,v in [(0,1,1),(1,2,-1),(2,3,1),(3,0,-1)]: z[i][j]=z[j][i]=v
assert all(sum(r)==0 for r in y+z)
assert norm(y)==6 and norm(z)==8
cases=[]
for p in [3,4,5,6]:
    c=F(3,5)**(p-1)+F(2,5)**(p-1); w=F(2,5)**(p-2)
    g=[[abs(x)**(p-2)*x for x in r] for r in a];m=mm(tr(a),g)
    assert m==tr(m)
    for v in [y,z]:
        t,s=ts(a,m,v,p)
        assert t==w*norm(v) and s==c*norm(v)
    k=1
    while (p-1)*w**k>=c**k: k+=1
    # Materialize two copies and check the sharp Hessian witness directly.
    u2=kron(a,a);x2=kron(y,z);m2=kron(m,m)
    t,s=ts(u2,m2,x2,p)
    assert t==w**2*norm(x2) and s==c**2*norm(x2)
    cases.append(dict(p=p,firstNegativePower=k,secondHessianEigenvalue=str(p*((p-1)*w*w-c*c))))
assert cases[0]['firstNegativePower']==3 and cases[1]['firstNegativePower']==2
lo=F(1004062,10**6);hi=F(1004063,10**6)
assert lo**100<F(3,2)<hi**100
rl=F(3,5)*lo+F(2,5);rh=F(3,5)*hi+F(2,5)
assert rh**4<F(101,100)<rl**5
out={'integerExponentChecks':cases,'p201over100FirstNegativePower':5,'exactRootBracketVerified':True,'directTwoCopyWitnessesVerified':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
