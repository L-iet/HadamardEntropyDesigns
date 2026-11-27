# SPDX-License-Identifier: Apache-2.0
"""Exact minimal-buffer checks using an integer Walsh transform."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from random import Random
import json


def walsh(values):
    values=list(values);width=1
    while width<len(values):
        for start in range(0,len(values),2*width):
            for j in range(start,start+width):
                a,b=values[j],values[j+width]
                values[j],values[j+width]=a+b,a-b
        width*=2
    return values


def case(support):
    target=len(support);d=target-4;size=1<<d;k=d*(d+1)//2
    assert size>=4*target*k
    masks=[1<<j for j in range(d)]+[(1<<i)|(1<<j) for i,j in combinations(range(d),2)]
    sums={a:sum((-1)**((a&x).bit_count()%2) for x in support) for a in masks}
    variance_numerator=sum(s*s for s in sums.values());assert variance_numerator>0
    coefficients=[0]*size
    for a,s in sums.items():coefficients[a]=s
    values=walsh(coefficients) # values = N*f, all exact integers.
    buffer_numerator=max(0,max(v-(size if i in support else 0) for i,v in enumerate(values)))
    assert 16*k*buffer_numerator**2>=variance_numerator
    numerators=[(size if i in support else 0)+buffer_numerator-v for i,v in enumerate(values)]
    denominator=size*(target+buffer_numerator)
    assert min(numerators)>=0 and sum(numerators)==denominator
    corrected_fourier=walsh(numerators)
    assert all(corrected_fourier[a]==0 for a in masks)
    collision=F(sum(v*v for v in numerators),denominator**2)
    beta=F(buffer_numerator,target);variance=F(variance_numerator,target*target)
    assert collision==F(1,size)+(F(1,target)-(1+variance)/size)/(1+beta)**2
    deficit=F(1,target)-collision
    assert deficit>F(1,8*target**3)>F(1,1024*target**4)
    return {'target':target,'minimalBuffer':str(beta),'correctedCollision':str(collision),
            'deficit':str(deficit),'exactMomentCorrectionPassed':True}


def main():
    rng=Random(20261120)
    cases=[case(set(range(20))),case(set(rng.sample(range(1<<16),20)))]
    for n in range(20,201,4):assert 2**(n-4)>=4*n*((n-4)*(n-3)//2)
    record={'passed':True,'minimalBufferExamples':cases,'parameterInequalities':46,
            'scope':'Exact examples support the analytic theorem for all multiples N>=20.'}
    Path(__file__).with_name('buffer_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Minimal-buffer checks passed: two exact 65536-point cube corrections.')


if __name__=='__main__':main()
