"""Exact checks for the sharp quadratic-character span theorem."""
from pathlib import Path
from random import Random
from math import isqrt
import json

HERE=Path(__file__).resolve().parent


def prime(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def legendre(p):
    return [0]+[1 if pow(j,(p-1)//2,p)==1 else -1 for j in range(1,p)]


def pac(a):return [sum(a[j]*a[(j+s)%len(a)] for j in range(len(a))) for s in range(len(a))]


def verify_norm(seqs,t):
    n=len(seqs[0]);assert all(len(a)==n and all(x%2 for x in a) for a in seqs)
    assert [sum(x) for x in zip(*(pac(a) for a in seqs))]==[4*t]+[0]*(n-1)


def build(l,u,v,w):
    return [[uu*x+ww+(vv if j==0 else 0) for j,x in enumerate(l)] for uu,vv,ww in zip(u,v,w)]


def main():
    rng=Random(20261121)
    minima=[];samples=[];symmetric_samples=[];congruence=[]
    for p in range(3,102,2):
        if not prime(p):continue
        l=legendre(p)
        assert pac(l)==[p-1]+[-1]*(p-1)
        if p%4==3:
            k=(p-3)//4;t=(p*p+6*p+21)//16
            seqs=build(l,[1,1,1,0],[1,1,1,-2*k],[0,0,0,1])
        else:
            k=(p-1)//4;t=(p*p+2*p+5)//8
            seqs=build(l,[1,1,0,0],[1,-1,-2*k,-2*k],[0,0,1,1])
        verify_norm(seqs,t)
        minima.append({'p':p,'symmetry':'skew' if p%4==3 else 'symmetric',
                       'minimumEnergy':t,'boundaryReached':t==p,'witness':seqs})
        if p%36==11:
            assert (2*p-1)%9==3
            assert not any(a*a+b*b==4*p-2 for a in range(1,2*p+1,2) for b in range(1,2*p+1,2))
            congruence.append(p)
        if p%4==3:
            count=0
            for _ in range(500):
                w=[1]+[rng.randrange(-2,3) for _ in range(3)]
                u=[2*rng.randrange(-2,3)+(1-ww)%2 for ww in w]
                v=[0]+[2*rng.randrange(-2,3)+(1-ww)%2 for ww in w[1:]]
                S=sum(x*x for x in u);W=sum(x*x for x in w)
                num=S-p*W-2*sum(x*y for x,y in zip(w[1:],v[1:]))
                assert num%2==0
                v[0]=num//2
                if v[0]%2:continue
                E=p*S+sum(x*x for x in v)
                assert E%8==4
                assert E//4>=t
                if count<3:verify_norm(build(l,u,v,w),E//4)
                count+=1
            samples.append({'p':p,'validScalarTemplatesTested':count})
        else:
            count=0
            for _ in range(500):
                w=[1,1,0,0]
                u=[0,2,2*rng.randrange(-2,3)+1,2*rng.randrange(-2,3)+1]
                v=[0,0,2*rng.randrange(-2,3)+1,2*rng.randrange(-2,3)+1]
                S=sum(x*x for x in u)
                v[1]=-(u[2]*v[2]+u[3]*v[3])//2
                v[0]=(S-2*p)//2-v[1]
                if v[0]%2 or v[1]%2:continue
                assert sum(x*y for x,y in zip(u,v))==0
                E=p*S+sum(x*x for x in v)
                assert E%8==4 and E//4>=t
                if count<3:verify_norm(build(l,u,v,w),E//4)
                count+=1
            symmetric_samples.append({'p':p,'validScalarTemplatesTested':count})
    assert [x['p'] for x in minima if x['boundaryReached']]==[3,5,7]
    report={'passed':True,'minimumWitnesses':minima,'skewSpanSamples':samples,
            'symmetricSpanSamples':symmetric_samples,
            'twoFixedChannelObstructionPrimes':congruence,
            'uniformProof':'sharp_character_span.tex',
            'scope':'sharp energy minima of a restricted template; no unrestricted nonexistence claim',
            'fullHadamardConjectureProved':False,'noveltyEstablished':False}
    (HERE/'checks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Verified sharp minimum witnesses at',len(minima),'odd primes through101.')
    print('Only boundary lengths:',[x['p'] for x in minima if x['boundaryReached']])
    print('Valid arbitrary skew scalar templates checked:',sum(x['validScalarTemplatesTested'] for x in samples))
    print('Valid nonminimal symmetric scalar templates checked:',sum(x['validScalarTemplatesTested'] for x in symmetric_samples))
    print('Two-fixed-channel congruence obstruction:',congruence)


if __name__=='__main__':main()
