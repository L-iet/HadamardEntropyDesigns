# SPDX-License-Identifier: Apache-2.0
"""Exact third completion moments without cubic point enumeration."""
from pathlib import Path
from itertools import product
from fractions import Fraction as F
import importlib.util,json,time
root=Path(__file__).resolve().parent
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    out=importlib.util.module_from_spec(spec);spec.loader.exec_module(out);return out
cc=module('codes',root.parents[1]/'round10/codes/check.py')
mm=module('old_moments',root.parents[1]/'round11/moments/check.py')
trap=json.loads((root.parents[1]/'round10/code_traps/search.json').read_text())['trap']

def third(g,p):
    start=time.monotonic();stats,groups=mm.pool_moments(g,p)
    pts=list(groups);weights=[groups[x] for x in pts];m=len(pts);indices={x:i for i,x in enumerate(pts)}
    adjacency=[0]*m;edges=[]
    for i in range(m):
        for j in range(i+1,m):
            if cc.dot(pts[i],pts[j])%p==0:
                adjacency[i]|=1<<j;adjacency[j]|=1<<i;edges.append((i,j))
    triangles=0;collinear=0;unit_weights=all(w==1 for w in weights)
    for i,j in edges:
        common=(adjacency[i]&adjacency[j])>>(j+1)
        if unit_weights:triangles+=common.bit_count()
        else:
            while common:
                low=common&-common;k=j+1+low.bit_length()-1
                triangles+=weights[i]*weights[j]*weights[k];common-=low
        for t in range(1,p):
            v=[(x+t*y)%p for x,y in zip(pts[i],pts[j])]
            scale=pow(next(x for x in v if x),-1,p)
            key=tuple(x*scale%p for x in v);k=indices.get(key,-1)
            if k>j:collinear+=weights[i]*weights[j]*weights[k]
    r1=sum(w**3 for w in weights)
    two=3*sum(weights[i]*weights[j]*(weights[i]+weights[j]) for i,j in edges)
    r2=two+6*collinear;r3=6*(triangles-collinear)
    h=stats['quotientHalfDimension'];d1=p**(h-1)+1;d2=p**(h-2)+1
    moment=F(r1,d1)+F(r2,d1*d2)
    if h==2:assert r3==0
    else:moment+=F(r3,d1*d2*(p**(h-3)+1))
    second=F(stats['secondMomentAdditionalCount']);ratio=moment/second
    ceil=lambda x:-(-x.numerator//x.denominator)
    stats.update(orderedRank1Weight=r1,orderedRank2Weight=r2,orderedRank3Weight=r3,
                 unorderedOrthogonalTriangleWeight=triangles,unorderedCollinearTriangleWeight=collinear,
                 thirdMomentAdditionalCount=str(moment),thirdToSecondRatio=str(ratio),
                 thirdMomentTotalLowerBound=stats['baseSignClasses']+ceil(ratio),seconds=time.monotonic()-start)
    return stats,groups

records=[]
for count in (8,5):
    g=cc.rref(trap['signs'][:count],5);stats,groups=third(g,5);records.append(stats)
    print('Computed',count,stats,flush=True)
    if count!=8:continue
    # Enumerate all 12 generators in the four-dimensional quotient.
    enlarged=g;quotient=[]
    for v in cc.kernel(g,5):
        larger=cc.rref(enlarged+(v,),5)
        if len(larger)>len(enlarged):quotient.append(v);enlarged=larger
    assert len(quotient)==4
    isotropic=set()
    for coeff in product(range(5),repeat=4):
        v=tuple(sum(a*b[j] for a,b in zip(coeff,quotient))%5 for j in range(20))
        if not any(v) or cc.dot(v,v)%5:continue
        scale=pow(next(x for x in v if x),-1,5);isotropic.add(tuple(x*scale%5 for x in v))
    assert len(isotropic)==36
    initial=tuple(tuple(x) for x in trap['basis']);codes={initial};todo=[initial]
    while todo:
        current=todo.pop();directions=set()
        for v in isotropic:
            alpha=[cc.dot(row,v)%5 for row in current]
            if not any(alpha):continue
            scale=pow(next(x for x in alpha if x),-1,5);key=tuple(x*scale%5 for x in alpha)
            if key in directions:continue
            directions.add(key);new=cc.pivot_code(current,v,5)
            if new not in codes:codes.add(new);todo.append(new)
        assert len(directions)==6
    assert len(codes)==12
    ys=sorted(len(cc.sign_words_from_systematic(c,5))-stats['baseSignClasses'] for c in codes)
    assert F(sum(y**3 for y in ys),12)==F(stats['thirdMomentAdditionalCount'])
    stats['allGeneratorAdditionalCounts']=ys
out=dict(passed=True,records=records,scope='Known-order finite benchmarks; no all-order positivity assertion.')
(root/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
