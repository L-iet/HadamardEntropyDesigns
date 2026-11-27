# SPDX-License-Identifier: Apache-2.0
"""Exact Gaussian-integer realification and cyclotomic phase checks."""
from pathlib import Path
from fractions import Fraction as F
import importlib.util,json,random

ROOT=Path(__file__).resolve().parent
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return (a[0],-a[1])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def transpose(a):return list(map(list,zip(*a)))
def mm(a,b):
    bt=transpose(b);return [[dot(row,col) for col in bt] for row in a]
def eye(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def complex_gram(a):
    return [[tuple(sum(mul(x,conj(y))[k] for x,y in zip(row,col)) for k in range(2))
             for col in a] for row in a]
def rotation(n):
    return [[-1 if i%2==0 and j==i+1 else
             (1 if i%2==1 and j==i-1 else 0) for j in range(n)] for i in range(n)]
def realify(b):
    n=len(b);h=[[0]*(2*n) for _ in range(2*n)]
    for i,row in enumerate(b):
        for j,z in enumerate(row):
            x,y=mul((1,1),z)
            h[2*i][2*j]=x;h[2*i][2*j+1]=-y
            h[2*i+1][2*j]=y;h[2*i+1][2*j+1]=x
    return h
def compress(h):
    n=len(h)//2;b=[]
    for i in range(n):
        row=[]
        for j in range(n):
            x=h[2*i][2*j];y=h[2*i+1][2*j]
            assert h[2*i][2*j+1]==-y and h[2*i+1][2*j+1]==x
            assert (x+y)%2==0 and (y-x)%2==0
            row.append(((x+y)//2,(y-x)//2))
        b.append(row)
    return b

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def divmod_poly(a,b):
    a=trim(a);b=trim(b);q=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        j=len(a)-len(b);c=a[-1]
        assert b[-1]==1
        q[j]=c
        for k,x in enumerate(b):a[k+j]-=c*x
        a=trim(a)
    return trim(q),a
PHI={}
def cyclotomic(n):
    if n in PHI:return PHI[n]
    a=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:
            a,r=divmod_poly(a,cyclotomic(d));assert r==[0]
    PHI[n]=a;return a

def main():
    examples=[]
    for q in (5,13,17):
        n=q+1;res={x*x%q for x in range(1,q)}
        chi=lambda x:0 if x%q==0 else (1 if x%q in res else -1)
        c=[[0 if i==j else (1 if i==0 or j==0 else chi(i-j))
             for j in range(n)] for i in range(n)]
        assert c==transpose(c) and mm(c,c)==[[q*int(i==j) for j in range(n)] for i in range(n)]
        b=[[(int(i==j),c[i][j]) for j in range(n)] for i in range(n)]
        assert complex_gram(b)==[[(n*int(i==j),0) for j in range(n)] for i in range(n)]
        h=realify(b);size=2*n;j=rotation(size)
        assert all(abs(x)==1 for row in h for x in row)
        assert mm(h,transpose(h))==[[size*int(i==k) for k in range(size)] for i in range(size)]
        assert mm(h,j)==mm(j,h) and compress(h)==b
        rng=random.Random(q);rp=list(range(size));cp=list(range(size))
        rng.shuffle(rp);rng.shuffle(cp)
        rsign=[rng.choice((-1,1)) for _ in rp];csign=[rng.choice((-1,1)) for _ in cp]
        moved=[[rsign[i]*csign[k]*h[rp[i]][cp[k]] for k in range(size)] for i in range(size)]
        jr=[[rsign[i]*rsign[k]*j[rp[i]][rp[k]] for k in range(size)] for i in range(size)]
        jc=[[csign[i]*csign[k]*j[cp[i]][cp[k]] for k in range(size)] for i in range(size)]
        assert mm(moved,jc)==mm(jr,moved)
        assert mm(jr,jr)==[[-int(i==k) for k in range(size)] for i in range(size)]
        examples.append({'conferencePrime':q,'quaternaryOrder':n,'realOrder':size,
                         'compressedMatrix':b,'realifiedMatrix':h,
                         'signedStructureIntertwiningChecked':True})
    spectra=[]
    for m in (3,5,6,7,8,9,10,12,15,16):
        d=__import__('math').gcd(m,4)
        # Exact fourth-power Fourier Gram, in Z[zeta_m].
        expected=[[m if 4*(i-k)%m==0 else 0 for k in range(m)] for i in range(m)]
        for i in range(m):
            for k in range(m):
                counts=[0]*m
                for t in range(m):counts[(4*(i-k)*t)%m]+=1
                assert divmod_poly(counts,cyclotomic(m))[1]==[expected[i][k]]
        assert mm(expected,expected)==[[m*d*x for x in row] for row in expected]
        spectra.append({'fourierOrder':m,'gcdWith4':d,
                        'fourthPowerRank':m//d,'squaredOperatorNorm':m*d,
                        'rhoSquared':str(F(d,m)),
                        'canPhaseAdjustToQuaternary':m==d})
    # An arbitrary pairing transported by H is a complex structure, but
    # usually not a signed permutation.
    spec=importlib.util.spec_from_file_location('old_paley',ROOT.parents[1]/'round9/check_rank.py')
    cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)
    h=cc.paley_two(5);n=len(h);j=rotation(n)
    transported=[[F(x,n) for x in row] for row in mm(mm(h,j),transpose(h))]
    assert mm(transported,transported)==[[-int(i==k) for k in range(n)] for i in range(n)]
    counts=[sum(x!=0 for x in row) for row in transported]
    assert any(x!=1 for x in counts)
    result={'passed':True,'classicalConferenceExamples':examples,
            'exactFourierFourthPowerSpectra':spectra,
            'canonicalPairingOnNormalizedPaley12':{'transportedRowsNonzeroCounts':counts,
              'isComplexStructure':True,'isSignedPermutation':False},
            'scope':'Known constructions and exact phase obstructions, not all-even-order Butson existence.'}
    (ROOT/'checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Quaternary compression and exact Fourier phase checks passed.')

if __name__=='__main__':main()
