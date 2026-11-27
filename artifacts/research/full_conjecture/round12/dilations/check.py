# SPDX-License-Identifier: Apache-2.0
"""Exact tests of prescribed-corner orthogonal dilations."""
from pathlib import Path
from itertools import product,combinations
from collections import Counter
import importlib.util,json,random
from fractions import Fraction as F

ROOT=Path(__file__).resolve().parent
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
cc=load('code_tools',ROOT.parents[1]/'round10/codes/check.py')
qq=load('quotient_tools',ROOT.parents[1]/'round11/quotients/check.py')
old=load('paley_tools',ROOT.parents[1]/'round9/check_rank.py')

def transpose(a):return list(map(list,zip(*a)))
def multiply(a,b):
    bt=transpose(b)
    return [[sum(x*y for x,y in zip(row,col)) for col in bt] for row in a]
def gram(a):return multiply(a,transpose(a))
def sylvester(n):
    return [[1 if (a&b).bit_count()%2==0 else -1 for b in range(n)] for a in range(n)]

def code_extensions(g,p):
    n=len(g[0]);r=len(g);m=n//2
    c=cc.self_dual_extension(g,p,random.Random(20261121))
    current=list(g);e=[]
    for row in c:
        if len(cc.rref(current+[row],p))>len(current):
            e.append(row);current=list(cc.rref(current+[row],p))
    assert len(e)==2
    raw=[qq.solve([list(row) for row in list(g)+e],
                  [0]*r+[int(i==j) for j in range(2)],p) for i in range(2)]
    pair=[[cc.dot(a,b)%p for b in raw] for a in raw];inv2=pow(2,-1,p)
    f=[[(raw[i][j]-inv2*sum(pair[i][k]*e[k][j] for k in range(2)))%p
        for j in range(n)] for i in range(2)]
    for ruling in (0,1):
        for u,v in [(1,z) for z in range(p)]+[(0,1)]:
            if ruling==0:
                extra=[[u*e[0][j]-v*f[1][j] for j in range(n)],
                       [u*e[1][j]+v*f[0][j] for j in range(n)]]
            else:
                extra=[[u*e[0][j]+v*e[1][j] for j in range(n)],
                       [v*f[0][j]-u*f[1][j] for j in range(n)]]
            yield cc.rref(list(g)+extra,p)

def main():
    a=sylvester(8);hb=old.paley_two(5);b=hb[:8];e=hb[8:];n=20
    frame=[x+y for x,y in zip(a,b)]
    assert gram(frame)==[[n*int(i==j) for j in range(8)] for i in range(8)]
    g=cc.rref(frame,5);assert len(g)==8
    desired=Counter(tuple(row) for row in transpose(b))
    profiles=[];witnesses=[];all_codes=[]
    for code in code_extensions(g,5):
        assert len(code)==10 and all(cc.dot(x,y)%5==0 for x in code for y in code)
        all_codes.append(code)
        family=cc.sign_words_from_systematic(code,5)
        assert set(map(tuple,frame))<=set(family)
        assert all(cc.dot(x,y)==0 for x,y in combinations(family,2))
        fixed=False
        if len(family)==20:
            rest=[row for row in family if row not in set(map(tuple,frame))]
            fixed=Counter(row[:8] for row in rest)==desired
            if fixed:
                unused=rest[:];ordered=[]
                for row in transpose(b):
                    i=next(i for i,x in enumerate(unused) if list(x[:8])==row)
                    ordered.append(unused.pop(i))
                d=[list(row[8:]) for row in ordered]
                witnesses.append({'code':code,'lowerRight':d})
        profiles.append({'signClasses':len(family),'prescribedTransposeCorner':fixed})
    assert len(profiles)==12 and len(set(all_codes))==12
    assert all(x['signClasses']==12 for x in profiles)
    assert not witnesses
    # Can a small change to the prescribed arithmetic-style frame escape?
    initial=all_codes[0];initial_signs=set(cc.sign_words_from_systematic(initial,5))
    repair=None;tested=set()
    for deleted in range(8):
        retained=frame[:deleted]+frame[deleted+1:]
        pool=cc.sign_words_from_systematic(cc.rref(cc.kernel(retained,5),5),5)
        for candidate in pool:
            if candidate in initial_signs:continue
            code=cc.pivot_code(initial,candidate,5)
            if code in tested:continue
            tested.add(code)
            family=cc.sign_words_from_systematic(code,5)
            assert set(map(tuple,retained))<=set(family)
            if len(family)==20:
                assert all(cc.dot(x,y)==0 for x,y in combinations(family,2))
                assert sum(tuple(row) in family for row in frame)==7
                repair={'deletedOriginalRow':deleted,'newCode':code,
                        'newRows':[list(x) for x in family],
                        'retainedOriginalRows':7,'minimumOriginalRowLoss':1,
                        'neighborCodesTested':len(tested)}
                break
        if repair:break
    assert repair is not None and repair['minimumOriginalRowLoss']==1
    # A rational scaled-orthogonal completion always exists in the
    # prescribed-corner family; it need not have sign entries.
    v=[[4,2,0,0],[-2,4,0,0],[0,0,4,-2],[0,0,2,4]]
    assert gram(v)==[[20*int(i==j) for j in range(4)] for i in range(4)]
    minus=multiply(multiply(transpose(b),transpose(a)),b)
    part=multiply(multiply(transpose(e),v),e)
    d=[[F(-x+y,12) for x,y in zip(rx,ry)] for rx,ry in zip(minus,part)]
    z=frame+[x+y for x,y in zip(transpose(b),d)]
    assert gram(z)==[[n*int(i==j) for j in range(n)] for i in range(n)]
    delta=sum(x**4 for row in d for x in row)-144
    assert delta>F(1,n+2)
    rounded=[[1 if x>=0 else -1 for x in row] for row in z]
    assert rounded[:8]==frame
    assert gram(rounded)!=[[n*int(i==j) for j in range(n)] for i in range(n)]
    error=sum((F(x)-y)**2 for rx,ry in zip(rounded,z) for x,y in zip(rx,ry))
    assert error<=delta
    # Rational residual similitude: V=E D E^T/b must have VV^T=nI.
    for witness in witnesses:
        d=witness['lowerRight']
        v=[[F(x,12) for x in row] for row in multiply(multiply(e,d),transpose(e))]
        assert gram(v)==[[n*int(i==j) for j in range(4)] for i in range(4)]
        minus=multiply(multiply(transpose(b),transpose(a)),b)
        part=multiply(multiply(transpose(e),v),e)
        assert [[F(-x+y,12) for x,y in zip(rx,ry)] for rx,ry in zip(minus,part)]==d
        witness['residualSimilitude']=[[str(x) for x in row] for row in v]
    result={'passed':True,'frame':[list(x) for x in frame],
      'allSelfDualExtensionBases':all_codes,
      'allCodeExtensionProfiles':profiles,'fullCompletions':sum(x['signClasses']==20 for x in profiles),
      'prescribedCornerCompletions':len(witnesses),'witnesses':witnesses,
      'oneRowRepair':repair,
      'rationalCompletion':{'residualSimilitude':v,
        'lowerRight':[[str(x) for x in row] for row in d],
        'quarticFlatnessDefect':str(delta),'squaredRoundingError':str(error),
        'entryValues':sorted({str(x) for row in d for x in row}),
        'fullScaledOrthogonalityChecked':True,'roundedMatrixNotHadamard':True},
      'scope':'One known-order prescribed frame; continuous dilation does not imply sign-valued completion.'}
    (ROOT/'checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Dilation checks passed; full completions:',result['fullCompletions'],
          'one-row repair found:',repair is not None,'quartic defect:',delta)

if __name__=='__main__':main()
