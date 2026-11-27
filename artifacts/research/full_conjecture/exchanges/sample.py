"""Reproduce the bounded seeded order-24 experiment (not an exhaustive census)."""
from itertools import combinations
from pathlib import Path
import json
import random

HERE=Path(__file__).resolve().parent


def main():
    n=24;s=6
    fixed=[0,((1<<(2*s))-1)<<(2*s),sum(1<<j for j in range(n) if (j//s)%2)]
    pool=[]
    for a in range(s+1):
        for q0 in combinations(range(1,s),a):
            m0=sum(1<<j for j in q0)
            for q1 in combinations(range(s,2*s),s-a):
                m1=m0+sum(1<<j for j in q1)
                for q2 in combinations(range(2*s,3*s),s-a):
                    m2=m1+sum(1<<j for j in q2)
                    for q3 in combinations(range(3*s,4*s),a):
                        pool.append(m2+sum(1<<j for j in q3))
    assert all(all((x^y).bit_count()==n//2 for y in fixed) for x in pool)
    rng=random.Random(20261120);hist={};dead=[]
    for trial in range(30):
        rows=fixed[:];cand=pool[:]
        while cand:
            chosen=rng.choice(cand);rows.append(chosen)
            cand=[x for x in cand if (x^chosen).bit_count()==n//2]
        hist[len(rows)]=hist.get(len(rows),0)+1
        if len(rows)<n:dead.append(rows)
    out={'n':n,'fixed':fixed,'seed':20261120,'trials':30,'poolSize':len(pool),
         'histogram':hist,'deadEnds':dead}
    (HERE/'partial24.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('Seeded maximal row-count histogram:',hist)


if __name__=='__main__':main()
