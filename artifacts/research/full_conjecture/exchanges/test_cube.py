"""Compare the RREF enumerator with independent exhaustive small cubes."""
from pathlib import Path
import json
import random
from cube_kernel import cube_kernel,row


def main():
    rng=random.Random(183627)
    cases=0
    for n in range(1,10):
        for m in range(n+1):
            a=[[rng.randrange(-2,3) for j in range(n)] for i in range(m)]
            actual,_=cube_kernel(a,n)
            expected=[]
            for mask in range(0,1<<n,2):
                v=row(mask,n)
                if all(sum(x*y for x,y in zip(r,v))==0 for r in a):expected.append(mask)
            assert actual==expected,(n,m,actual,expected)
            cases+=1
    out={'passed':True,'cases':cases,'seed':183627,
         'method':'independent exhaustive normalized cubes, integer constraints'}
    Path(__file__).with_name('kernel-tests.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(out)


if __name__=='__main__':main()
