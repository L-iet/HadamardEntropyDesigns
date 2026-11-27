# SPDX-License-Identifier: Apache-2.0
"""Exact generalized-weight / retained-row resource profile, 4096 subsets."""
from pathlib import Path
from itertools import product
from collections import Counter
import importlib.util,json
root=Path(__file__).resolve().parent
w=json.loads((root.parents[1]/'round10/code_traps/search.json').read_text())['trap']
spec=importlib.util.spec_from_file_location('codes',root.parents[1]/'round10/codes/check.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)
basis=w['basis'];rows=w['signs'];piv=[next(i for i,x in enumerate(row) if x) for row in basis]
coeff=[[row[j]%5 for j in piv] for row in rows]
h=cc.kernel(list(map(list,zip(*coeff))),5)
assert len(h)==2
columns=list(zip(*h));assert all(any(c) for c in columns)
def point(c):
    scale=pow(next(x for x in c if x),-1,5)
    return tuple(x*scale%5 for x in c)
multiplicities=Counter(point(c) for c in columns)
allpoints={(1,x) for x in range(5)}|{(0,1)}
profile=sorted((multiplicities[x] for x in allpoints),reverse=True)
assert profile==[4,4,2,2,0,0]
dualweights=Counter(sum(sum(a*x for a,x in zip(c,col))%5!=0 for col in columns)
                    for c in product(range(5),repeat=2))
assert dualweights=={0:1,8:8,10:8,12:8}
weights=[13]*10;witnesses=[None]*10
for mask in range(1<<12):
    inds=[j for j in range(12) if mask>>j&1]
    rank=len(cc.rref([columns[j] for j in inds],5)) if inds else 0
    nullity=len(inds)-rank
    for i in range(nullity):
        if len(inds)<weights[i]:weights[i]=len(inds);witnesses[i]=inds
expected=[2,3,4,6,7,8,9,10,11,12]
assert weights==expected
result=dict(passed=True,subsetsChecked=1<<12,parityCheckBasis=h,
            projectiveColumnMultiplicities=profile,dualWeightEnumerator=dict(dualweights),
            generalizedWeights=weights,maximumOldRowsRetained=[12-x for x in weights],
            minimumSupportWitnesses=witnesses)
(root/'retention.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
