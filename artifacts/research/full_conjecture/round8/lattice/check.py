"""Exact row-exchange search for the norm40 odd-coset benchmark."""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
MASKS=[0,16773120,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356]
N=24
ODD=[-1,-1,3,-1,1,1,-3,-1,1,1,-1,1,1,-1,-1,-1,1,-1,1,-1,1,-1,1,1]
FIVE=[3198332,6782212,8735670,11139280,13957672]


def rows(masks):return [[1-2*((m>>j)&1) for j in range(N)] for m in masks]
def dot(a,b):return sum(x*y for x,y in zip(a,b))


def pool(masks):
    a=[list(map(F,row)) for row in rows(masks)]
    pivots=[]
    for col in range(N):
        rank=len(pivots)
        p=next((i for i in range(rank,len(a)) if a[i][col]),None)
        if p is None:continue
        a[rank],a[p]=a[p],a[rank]
        scale=a[rank][col];a[rank]=[x/scale for x in a[rank]]
        for i in range(len(a)):
            if i!=rank and a[i][col]:
                scale=a[i][col];a[i]=[x-scale*y for x,y in zip(a[i],a[rank])]
        pivots.append(col)
        if len(pivots)==len(a):break
    free=[j for j in range(N) if j not in pivots]
    den=lcm(*(a[i][j].denominator for i in range(len(a)) for j in free))
    coeff=[[-int(a[i][j]*den) for j in free] for i in range(len(a))]
    answer=[]
    for tail in product((-1,1),repeat=len(free)-1):
        val=(1,)+tail
        numerators=[]
        for ar in coeff:
            z=sum(x*y for x,y in zip(ar,val))
            if abs(z)!=den:break
            numerators.append(z)
        else:
            v=[0]*N
            for j,x in zip(free,val):v[j]=x
            for j,x in zip(pivots,numerators):v[j]=x//den
            if v[0]<0:v=[-x for x in v]
            answer.append(sum((x<0)<<j for j,x in enumerate(v)))
    return sorted(answer)


def clique(candidates,target):
    if target==0:return []
    while len(candidates)>=target:
        first,*tail=candidates
        compatible=[v for v in tail if (v^first).bit_count()==N//2]
        found=clique(compatible,target-1)
        if found is not None:return [first]+found
        candidates=tail
    return None


if __name__=='__main__':
    assert pool(MASKS)==[]
    assert dot(ODD,ODD)==40 and all(dot(row,ODD)==0 for row in rows(MASKS))
    rounded=[1 if x>0 else -1 for x in ODD]
    bad=[i for i,row in enumerate(rows(MASKS)) if dot(row,rounded)]
    assert bad==[2,4,6,8,10]
    trials=[]
    result=None
    for deleted_count in (1,2,3):
        for deleted in combinations(range(len(MASKS)),deleted_count):
            retained=[m for i,m in enumerate(MASKS) if i not in deleted]
            candidates=pool(retained)
            inserted=clique(candidates,deleted_count+1)
            trials.append({'deleted':deleted,'candidates':len(candidates),'augmenting':inserted is not None})
            if inserted is not None:
                result={'deleted':deleted,'inserted':inserted,'retained':retained}
                break
        if result:break
    assert result is not None
    assert result['deleted']==(1,)
    candidates=pool(result['retained'])
    assert len(candidates)==16 and clique(candidates,6) is None
    assert clique(candidates,5)==FIVE
    augmented=result['retained']+FIVE
    assert len(augmented)==16 and all((a^b).bit_count()==12 for a,b in combinations(augmented,2))
    witness=[int(j==0)+int(j==9)-int(j==11) for j in range(N)]
    energy=N*dot(witness,witness)-sum(dot(row,witness)**2 for row in rows(augmented))
    assert sum(witness)%2 and energy==0
    assert pool(augmented)==[]
    # Global column sign changes preserve all inner products and the kernel.
    diagonal=[-1 if j%3==0 else 1 for j in range(N)]
    changed=[[x*y for x,y in zip(row,diagonal)] for row in rows(MASKS)]
    changed_odd=[x*y for x,y in zip(ODD,diagonal)]
    assert all(dot(row,changed_odd)==0 for row in changed)
    assert dot(changed_odd,changed_odd)==40
    report={'status':'passed','arithmetic':'exact rational/integer','original_masks':MASKS,
            'odd_kernel_vector':ODD,'odd_vector_norm_squared':40,
            'rounded_sign_bad_row_indices':bad,'trials':trials,'minimal_augmenting_deletions':1,
            'repair':result,'maximum_insertions_after_deleting_row1':5,
            'five_inserted_masks':FIVE,'candidate_classes':candidates,
            'candidate_graph_has_no_six_clique':True,'terminal_augmented_masks':augmented,
            'augmented_odd_sum_row_span_witness':witness,'augmented_witness_budget':energy,
            'scope':'Explicit repair and finite graph certificates; no universal exchange bound is claimed.'}
    (HERE/'checks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report))
