"""Exact original stdlib certificates for prime-selected known-order parameters."""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
import json

def prime(p):
 if p<2:return False
 if p%2==0:return p==2
 return all(p%d for d in range(3,isqrt(p)+1,2))
def ceil_theta(x):
 target=x**21;lo=0;hi=x+1
 while hi-lo>1:
  mid=(lo+hi)//2
  if mid**40>=target:hi=mid
  else:lo=mid
 assert (hi-1)**40<target<=hi**40
 return hi

def gram(h):
 n=len(h)
 assert all(sum(x*y for x,y in zip(a,b))==n*int(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
def any_prime_hadamard(p):
 assert prime(p) and p%2
 chi=lambda x:0 if x%p==0 else 1 if pow(x%p,(p-1)//2,p)==1 else -1
 if p%4==3:
  a=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
  h=[r+r for r in a]+[r+[-x for x in r] for r in a];method='doubled PaleyI'
 else:
  c=[[0]+[1]*p]+[[1]+[chi(j-i) for j in range(p)] for i in range(p)]
  m=p+1;a=[[c[i][j]+int(i==j) for j in range(m)] for i in range(m)];b=[[c[i][j]-int(i==j) for j in range(m)] for i in range(m)]
  h=[x+y for x,y in zip(a,b)]+[x+[-z for z in y] for x,y in zip(b,a)];method='PaleyII'
 assert all(x in (-1,1) for r in h for x in r) and len(h)==2*(p+1)
 gram(h);return method

cases=[];small=[]
for s in range(4,25):
 h=1<<s;x=h//2;a=ceil_theta(x);y=x-a;p=y if y%2 else y-1
 while not prime(p):p-=2
 k=2*(p+1);g=h-k;n=k*h
 assert s<=g<h//2 and h//2<k<h
 assert 2*a-2<=g<=4*a-2
 assert p>=y-ceil_theta(y)
 # A spanning omitted set is explicit: polynomial-coordinate basis, then
 # smallest remaining nonzero field labels until g distinct labels.
 omitted=[1<<j for j in range(s)]
 for t in range(1,h):
  if len(omitted)==g:break
  if t not in omitted:omitted.append(t)
 assert len(set(omitted))==g and 0 not in omitted and all(1<<j in omitted for j in range(s))
 ratio=F(k,h);deficit=F(1,n)-F(1,h*h);tv=1-F(1,k)
 assert deficit==F(g,k*h*h) and 1-ratio==F(g,h)
 cases.append(dict(seedExponent=s,h=h,thetaCeiling=a,primeSearchUpper=y,prime=p,knownHadamardOrder=k,n=n,omittedSlopeCount=g,spanningBasisIncluded=True,relativeCollision=str(ratio),relativeDeficit=str(1-ratio),absoluteDeficit=str(deficit),exactHadamardMixtureDistance=str(tv),lawAtoms=h*h,ordinaryPrimeOnly=True))
 if p<=53:small.append(dict(prime=p,order=k,construction=any_prime_hadamard(p),GramVerified=True))
# Exact exponent arithmetic for the published asymptotic transfer.
assert (1-F(21,40))/2==F(19,80) and (3-F(21,40))/2==F(99,80)
assert (1-F(1,2))/2==F(1,4) and (3-F(1,2))/2==F(5,4)
result={'passed':True,'ordinaryPrimeParameters':cases,'smallPaleyBothResidueClasses':small,'unconditionalTheta':'21/40','unconditionalRelativeExponent':'19/80','unconditionalAbsoluteExponent':'99/80','conditionalRHRelativeRate':'n^(-1/4) log n','conditionalRHAbsoluteRate':'n^(-5/4) log n','RHNotAssumedForAnyFiniteCheck':True,'NoClaimOfExplicitBHPAsymptoticCutoff':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'parameterCases':len(cases),'first':cases[0],'last':cases[-1],'matrixChecks':small,'asymptoticExponentsVerified':True},indent=2))
