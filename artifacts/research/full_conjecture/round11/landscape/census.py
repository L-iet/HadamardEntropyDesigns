# SPDX-License-Identifier: Apache-2.0
"""Exact full sign-bearing self-dual-neighbor census via Gray syndromes."""
from pathlib import Path
from collections import Counter
import json,importlib.util,time
from math import comb
root=Path(__file__).resolve().parent
w=json.loads((root.parents[1]/'round10/code_traps/search.json').read_text())['trap']
basis=w['basis'];old=w['signs'];p=5;n=20
pivots=[next(j for j,x in enumerate(row) if x) for row in basis]
coefficients=[[row[j]%p for j in pivots] for row in old]
assert len(basis)==10 and len(set(pivots))==10 and len(old)==12
assert all(basis[i][j]==(i==k) for i in range(10) for k,j in enumerate(pivots))
assert all(sum(x*y for x,y in zip(a,b))%p==0 for a in basis for b in basis)
assert all(sum(c*basis[i][j] for i,c in enumerate(coef))%p==row[j]%p
           for coef,row in zip(coefficients,old) for j in range(n))
assert all(sum(x*y for x,y in zip(a,b))==20*(i==j)
           for i,a in enumerate(old) for j,b in enumerate(old))
inv=(0,1,3,2,4)
alpha=[sum(row)%p for row in basis];assert not any(alpha)
columns=[[basis[i][j] for i in range(10)] for j in range(n)]
neighbors={};inside=0;previous=0;start=time.monotonic()
for index in range(1<<19):
    gray=index^(index>>1)
    if index:
        changed=gray^previous;j=changed.bit_length()
        delta=-2 if (gray>>(j-1))&1 else 2
        alpha=[(a+delta*x)%p for a,x in zip(alpha,columns[j])]
    previous=gray
    first=next((a for a in alpha if a),0)
    if not first:inside+=1;continue
    scale=inv[first];key=tuple(a*scale%p for a in alpha)
    record=neighbors.get(key)
    if record is None:neighbors[key]=[1,gray<<1]
    else:record[0]+=1
assert inside==12
profiles=Counter();totals=Counter();improving=0;maximal=0;best=None;min_loss=20;improvers=[]
for key,(new,mask) in neighbors.items():
    retained=sum(sum(a*c for a,c in zip(key,row))%p==0 for row in coefficients)
    total=new+retained;profiles[retained,new,total]+=1;totals[total]+=1
    if total>12:
        improving+=1;min_loss=min(min_loss,12-retained);improvers.append((mask,retained,total))
    if total>maximal:maximal=total;best=dict(syndrome=key,mask=mask,retained=retained,new=new,total=total)
assert sum(record[0] for record in neighbors.values())==(1<<19)-12
spec=importlib.util.spec_from_file_location('codes',root.parents[1]/'round10/codes/check.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)
v=tuple(-1 if best['mask']>>j&1 else 1 for j in range(n))
newbasis=cc.pivot_code(tuple(tuple(row) for row in basis),v,p)
family=cc.sign_words_from_systematic(newbasis,p)
assert len(family)==best['total']
for mask,retained,total in improvers:
    word=tuple(-1 if mask>>j&1 else 1 for j in range(n))
    neighbor=cc.pivot_code(tuple(tuple(row) for row in basis),word,p)
    signs=cc.sign_words_from_systematic(neighbor,p)
    assert len(signs)==total==20
    assert len(set(signs)&set(map(tuple,old)))==retained
    assert all(cc.dot(a,b)==20*(i==j) for i,a in enumerate(signs) for j,b in enumerate(signs))
evaluation_dual=cc.kernel(list(map(list,zip(*coefficients))),5)
assert len(evaluation_dual)==2
dual_words=cc.span(evaluation_dual,5)
dual_weights=Counter(sum(x!=0 for x in word) for word in dual_words)
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
evaluation_weights={}
for weight in range(13):
    numerator=sum(count*sum((-1)**j*4**(weight-j)*choose(dw,j)*choose(12-dw,weight-j)
                            for j in range(weight+1)) for dw,count in dual_weights.items())
    assert numerator%25==0
    evaluation_weights[weight]=numerator//25
assert sum(evaluation_weights.values())==5**10 and evaluation_weights[0]==1
all_retention={12-weight:count//4 for weight,count in evaluation_weights.items() if weight and count}
assert all(evaluation_weights[w]%4==0 for w in range(1,13))
bearing_retention=Counter()
for (retained,new,total),count in profiles.items():bearing_retention[retained]+=count
old_only={retained:count-bearing_retention[retained] for retained,count in all_retention.items()}
assert all(v>=0 for v in old_only.values())
full_totals=totals.copy()
for retained,count in old_only.items():full_totals[retained]+=count
assert sum(full_totals.values())==(5**10-1)//4
result=dict(passed=True,normalizedSigns=1<<19,oldCodeSignClasses=inside,
            signBearingNeighbors=len(neighbors),allHyperplaneNeighbors=(5**10-1)//4,
            improvingSignBearingNeighbors=improving,maximumNeighborSignCount=maximal,
            minimumOldRowLossAmongImproving=min_loss,
            totalSignCountHistogram={str(k):v for k,v in sorted(totals.items())},
            profiles=[dict(retained=a,new=b,total=c,neighbors=v) for (a,b,c),v in sorted(profiles.items())],
            maximumWitness=best,seconds=time.monotonic()-start)
result.update(evaluationDualWeightEnumerator=dict(sorted(dual_weights.items())),
              allNeighborOldRetentionHistogram=dict(sorted(all_retention.items())),
              neighborsWithNoOutsideSignByRetention=dict(sorted(old_only.items())),
              fullNeighborSignCountHistogram=dict(sorted(full_totals.items())))
(root/'census.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('profiles',)}))
