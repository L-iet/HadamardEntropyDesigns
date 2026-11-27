# SPDX-License-Identifier: Apache-2.0
"""Exact first/second moment data for sign words in isotropic quotients."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import importlib.util,json

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('code_tools',ROOT.parents[1]/'round10/codes/check.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)

def projective_quotient(v,g,p):
    v=[x%p for x in v]
    for row in g:
        pivot=next(i for i,x in enumerate(row) if x)
        c=v[pivot]
        v=[(x-c*y)%p for x,y in zip(v,row)]
    if not any(v):return None
    scale=pow(next(x for x in v if x),-1,p)
    return tuple(x*scale%p for x in v)

def pool_moments(g,p):
    n=len(g[0]);g=cc.rref(g,p);h=n//2-len(g)
    assert h>=2
    pool=cc.sign_words_from_systematic(cc.rref(cc.kernel(g,p),p),p)
    groups={};b=0
    for v in pool:
        key=projective_quotient(v,g,p)
        if key is None:b+=1
        else:groups[key]=groups.get(key,0)+1
    w=sum(groups.values());s2=sum(x*x for x in groups.values())
    pairs=sum(a*b for x,a in groups.items() for y,b in groups.items()
              if x!=y and cc.dot(x,y)%p==0)
    d1=p**(h-1)+1;d2=p**(h-2)+1
    mean=F(w,d1);second=F(s2,d1)+F(pairs,d1*d2)
    lower=second/mean if w else F(0)
    ceil=lambda x:-(-x.numerator//x.denominator)
    return {'p':p,'order':n,'retainedRank':len(g),'quotientHalfDimension':h,
      'poolClasses':len(pool),'baseSignClasses':b,'weightedPoints':len(groups),
      'outsideClasses':w,'sumSquaredPointWeights':s2,'orderedOrthogonalWeight':pairs,
      'expectedAdditionalSignCount':str(mean),'secondMomentAdditionalCount':str(second),
      'maximumTotalCountLowerBound':b+ceil(lower)},groups

def all_hyperbolic_points(p,h):
    points=set()
    for v in product(range(p),repeat=2*h):
        if not any(v) or sum(v[i]*v[h+i] for i in range(h))%p:continue
        scale=pow(next(x for x in v if x),-1,p)
        points.add(tuple(x*scale%p for x in v))
    assert len(points)==(p**(h-1)+1)*(p**h-1)//(p-1)
    return points

def main():
    # Check the exact point count underlying generator incidence recurrence.
    points=[{'p':p,'h':h,'points':len(all_hyperbolic_points(p,h))}
            for p,h in ((3,1),(3,2),(3,3),(5,2))]
    data=json.loads((ROOT.parents[1]/'round10/codes/checks.json').read_text())
    c=tuple(tuple(x) for x in data['allSelfDualExtensionsOfSeed'][0]['selfDualBasis'])
    s=cc.sign_words_from_systematic(c,3)
    g=cc.rref(s[:4],3)
    stats,groups=pool_moments(g,3)
    dual=cc.span(cc.kernel(g,3),3);codes={c};todo=[c]
    while todo:
        current=todo.pop();words=cc.span(current,3);directions=set()
        for v in sorted(dual-words):
            if cc.dot(v,v)%3:continue
            alpha=[cc.dot(row,v)%3 for row in current]
            scale=pow(next(x for x in alpha if x),-1,3)
            key=tuple(x*scale%3 for x in alpha)
            if key in directions:continue
            directions.add(key)
            neighbor=cc.pivot_code(current,v,3)
            if neighbor not in codes:codes.add(neighbor);todo.append(neighbor)
            if len(directions)==4:break
        assert len(directions)==4
    assert len(codes)==8
    ys=[len(cc.sign_words_from_systematic(basis,3))-stats['baseSignClasses'] for basis in codes]
    assert sum(map(F,ys))/len(ys)==F(stats['expectedAdditionalSignCount'])
    assert sum(F(y*y) for y in ys)/len(ys)==F(stats['secondMomentAdditionalCount'])
    # H20 seed is known-order input; no unknown-order matrix is assumed.
    trap=json.loads((ROOT.parents[1]/'round10/code_traps/search.json').read_text())['trap']
    records=[stats]
    for count in (5,8):
        g=cc.rref(trap['signs'][:count],5)
        stats,_=pool_moments(g,5);records.append(stats)
    out={'passed':True,'hyperbolicPointCounts':points,'knownOrderMomentData':records,
         'order12AllGeneratorAdditionalSignCounts':sorted(ys),
         'scope':'Moment formulas are proved in the paper; finite data do not prove all-order positivity.'}
    (ROOT/'checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
