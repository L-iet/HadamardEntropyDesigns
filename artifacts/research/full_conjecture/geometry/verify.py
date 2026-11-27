"""Exact certificates for quartic traps; standard library only."""
from itertools import combinations
from fractions import Fraction
from pathlib import Path
import json
from explore import householder, sylvester, tensor, hessian

ROOT=Path(__file__).resolve().parent


def mm(a,b):return [[sum(x*y for x,y in zip(ar,bc)) for bc in zip(*b)] for ar in a]
def tr(a):return list(map(list,zip(*a)))
def ident(n,c=1):return [[c*int(i==j) for j in range(n)] for i in range(n)]


def main():
    a=householder(5)
    # A=a/5, M=A^T A^{circ3}=(35I-6J)/125.
    ma=mm(tr(a),[[x**3 for x in row] for row in a])
    assert ma==[[175*int(i==j)-30 for j in range(5)] for i in range(5)]
    assert min(x*x for row in a for x in row)==4
    assert Fraction(sum(x**4 for row in a for x in row),625)==Fraction(29,25)
    cases=[]
    for k in (4,8,16):
        # U=V/(5 sqrt(k)), so fourth-power denominator is 625 k^2.
        v=tensor(a,sylvester(k));n=5*k
        assert mm(v,tr(v))==ident(n,25*k)
        m=mm(tr(v),[[x**3 for x in row] for row in v])
        assert m==[[k*ma[i//k][j//k]*int(i%k==j%k) for j in range(n)] for i in range(n)]
        assert min(x*x for row in v for x in row)==4
        assert Fraction(sum(x**4 for row in v for x in row),625*k*k)==Fraction(29,25)
        cases.append({'hadamardFactorOrder':k,'order':n,
                      'quarticValue':'29/25',
                      'minimumSquaredEntry':str(Fraction(4,25*k)),
                      'maximumPolarEigenvalue':str(Fraction(7,25*k)),
                      'hessianLowerBoundPerFrobeniusNormSquared':str(Fraction(4,5*k))})
    # The Householder order-7 saddle has every coordinate rotation
    # positively curved. Tensor with H4 to reach an admissible order.
    v=tensor(householder(7),sylvester(4));n=28;den=14**4
    h=hessian(v)
    diag=sorted(set(Fraction(h[i][i],den) for i in range(len(h))))
    assert diag==[Fraction(34,343),Fraction(412,343)]
    pairs=list(combinations(range(n),2))
    coords=[0]*len(pairs)
    # X=(E01+E12-E02) tensor I4: row sums vanish in the order7 factor.
    for offset in range(4):
        for aa,bb,sgn in ((0,1,1),(1,2,1),(0,2,-1)):
            coords[pairs.index((4*aa+offset,4*bb+offset))]=sgn
    q=Fraction(sum(coords[i]*h[i][j]*coords[j] for i in range(len(h)) for j in range(len(h))),den)
    assert q==Fraction(-24,7)
    result={'passed':True,'strictQuarticTrapCertificates':cases,
            'uniformProof':'quartic_traps.tex; valid for every Hadamard factor',
            'coordinateCurvatureTrap':{'order':28,'allGivensCurvatures':[str(x) for x in diag],
                                       'jointDirectionCurvature':str(q)},
            'fullHadamardConjectureProved':False,'noveltyClaim':False}
    (ROOT/'checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
