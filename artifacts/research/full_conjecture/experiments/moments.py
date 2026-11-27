"""Binary quadratic moment semigroup: exact signed designs and a genuine hole."""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]


def moment(mask,d):
    bits=[(mask>>i)&1 for i in range(d)]
    return [1]+bits+[bits[i]*bits[j] for i,j in combinations(range(d),2)]


def target(n,d):
    return [n]+[n//2]*d+[n//4]*(d*(d-1)//2)


def signed_coefficients(n,d):
    assert n%4==0
    out={0:n*(d*d-5*d+8)//8}
    out.update({1<<i:n*(3-d)//4 for i in range(d)})
    out.update({(1<<i)|(1<<j):n//4 for i,j in combinations(range(d),2)})
    actual=[sum(c*moment(mask,d)[i] for mask,c in out.items()) for i in range(len(target(n,d)))]
    assert actual==target(n,d)
    return out


def cube_move(mask,d):
    support=[i for i in range(d) if (mask>>i)&1]
    out={}
    for b in product((0,1),repeat=len(support)):
        sub=sum(x<<i for x,i in zip(b,support))
        out[sub]=(-1)**(len(support)-sum(b))
    actual=[sum(c*moment(x,d)[i] for x,c in out.items()) for i in range(1+d+d*(d-1)//2)]
    assert actual==[0]*len(actual)
    return out


def verify_rows(rows,d):
    actual=[sum(moment(mask,d)[i] for mask in rows) for i in range(len(target(len(rows),d)))]
    assert actual==target(len(rows),d)


def main():
    cases=[]
    for d in (3,4,7,11,19):
        n=4*((d+4)//4)
        co=signed_coefficients(n,d)
        cases.append({'d':d,'n':n,'signedCoefficients':co})
    d=4
    co=signed_coefficients(4,d)
    # n=4 cannot have d=4 unbiased pairwise-orthogonal binary columns:
    # adjoining the all-one column would give five orthogonal nonzero
    # vectors in R^4. The fractional coefficients all equal 1/4.
    fractional=[sum(Fraction(1,4)*moment(mask,d)[i] for mask in range(1<<d))
                for i in range(len(target(4,d)))]
    assert fractional==target(4,d)
    # Sixteen column patterns, multisets of four rows: exhaustive independent
    # certificate of this small hole (3876 candidate multisets).
    from itertools import combinations_with_replacement
    tested=0
    for rows in combinations_with_replacement(range(1<<d),4):
        tested+=1
        assert [sum(moment(mask,d)[i] for mask in rows) for i in range(len(target(4,d)))] != target(4,d)
    # An 8-run witness from four distinct nonzero Walsh characters.
    rows8=[sum(((a&b).bit_count()%2)<<j for j,a in enumerate((1,2,3,4))) for b in range(8)]
    verify_rows(rows8,d)
    moves={mask:cube_move(mask,d) for mask in range(1<<d) if mask.bit_count()>=3}
    # Möbius differences of order >=3 are a triangular Z-basis of the
    # integer kernel; each coefficient at its leading mask is exactly 1.
    assert len(moves)==2**d-(1+d+d*(d-1)//2)
    out={'status':'exact finite certificates, not a general saturation theorem',
         'signedDesignExamples':cases,
         'hole':{'d':d,'n':4,'target':target(4,d),'integerSignedRepresentation':co,
                 'uniformFractionalCoefficient':'1/4','multisetsExhausted':tested,
                 'nonnegativeIntegerRepresentationExists':False,
                 'doubleHoleWitnessMasks':rows8},
         'integerKernelBasisAtD4':moves}
    (ROOT/'data/moments.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('Certified quadratic moment hole:', {'d':d,'n':4,'multisets':tested})
    print('Signed construction and integer-kernel moves verified.')


if __name__=='__main__':main()
