# SPDX-License-Identifier: Apache-2.0
"""Exact arithmetic checks of the known-order Paley subsequence recipe."""
from pathlib import Path
from fractions import Fraction as F
import json

def main():
    u=-1;records=[]
    for t in range(4,13):
        while True:
            u+=1;q=3**(2*u+1);h=1<<q.bit_length();k=q+1
            s=h.bit_length()-1;g=h-k
            if ((t-2)*h<t*q<(t-1)*h and h>=t**3
                    and s<=g<h//2):break
        n=k*h
        assert q%4==3 and k%8==4 and h&(h-1)==0
        assert F(k,h)>1-F(2,t)
        assert 1-F(1,k)>1-F(2,t*t)
        records.append({'t':t,'primePowerExponent':2*u+1,'q':q,
          'paleyOrder':k,'sylvesterOrder':h,'productOrder':n,'seedBits':s,
          'omittedSlopes':g,'lawAtoms':h*h,'relativeCollisionRatio':str(F(k,h)),
          'exactDistanceToHadamardMixtures':str(1-F(1,k)),
          'absoluteCollisionDeficit':str(F(g,k*h*h))})
    out={'passed':True,'integerSequenceBenchmarks':records,
      'scope':'Infinite existence uses the written density proof and Paley theorem; no huge matrices were enumerated.'}
    Path(__file__).with_name('sequence_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('Exact Paley/Sylvester subsequence arithmetic checks passed.')

if __name__=='__main__':main()
