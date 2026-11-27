"""Small tests of a broader integral group-ring norm representation question.

For odd m and odd t>=m, ask whether four elements of J+2 Z[C_m]
have Hermitian squared norms summing to 4t. This question is OPEN here.
The boundary t=m forces binary coefficients by a coefficient-energy argument.
"""
from itertools import product
from pathlib import Path
import json
from investigate import pac, four_complementary

ROOT=Path(__file__).resolve().parents[1]


def one_defect_lift(m):
    binary=[(1,)+x for x in product((-1,1),repeat=m-1)]
    pair={}
    for a in binary:
        pa=pac(a)
        for b in binary:
            pair.setdefault(tuple(x+y for x,y in zip(pa[1:],pac(b)[1:])),(a,b))
    # Energy increment 8 means precisely one coefficient has magnitude 3,
    # all others magnitude 1. Put that coefficient in the fourth sequence
    # and at index 0 using row permutation and a cyclic shift.
    special=[(3,)+x for x in product((-1,1),repeat=m-1)]
    for c in binary:
        pc=pac(c)
        for d in special:
            key=tuple(-x-y for x,y in zip(pc[1:],pac(d)[1:]))
            if key in pair:
                a,b=pair[key]
                seqs=(a,b,c,d)
                assert [sum(v) for v in zip(*(pac(x) for x in seqs))]==[4*(m+2)]+[0]*(m-1)
                assert all(x%2 for seq in seqs for x in seq)
                return seqs
    return None


def main():
    out=[]
    for m in (3,5,7,9):
        for t in (m,m+2):
            witness=four_complementary(m) if t==m else one_defect_lift(m)
            assert witness
            out.append({'m':m,'t':t,'witness':witness,'oddCoefficients':True,
                        'summedPeriodicAutocorrelations':[sum(v) for v in zip(*(pac(x) for x in witness))]})
    (ROOT/'data/norm-lifting.json').write_text(json.dumps({
        'status':'8 small witnesses only; general norm lifting is not proved',
        'tested':out},indent=2)+'\n',encoding='utf-8')
    print('Verified eight odd-coefficient group-ring norm representations.')


if __name__=='__main__':main()
