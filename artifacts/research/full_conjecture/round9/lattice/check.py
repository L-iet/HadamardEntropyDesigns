"""Finite-field sign residues and exact norm-lifting profiles; stdlib only."""
from itertools import product,combinations
from pathlib import Path
from collections import Counter
import json

HERE=Path(__file__).resolve().parent
MASKS12=[0,16773120,16519104,9656012,13838682,14783914,1944718,11409518,15230494,5921970,3487346,13018356]
MASKS16=[0,16773120,16519104,10359454,7684730,5820908,9389414,1547504,6736278,11838780,3701846,13790378,10646512,2963882,12892774,5974836]
N=24


def rows(masks,n=N):return [[1-2*((m>>j)&1) for j in range(n)] for m in masks]
def dot(a,b):return sum(x*y for x,y in zip(a,b))


def modular_pool(masks,q,n=N):
    original=rows(masks,n)
    a=[[x%q for x in row] for row in original]
    pivots=[]
    for col in range(n):
        rank=len(pivots)
        chosen=next((i for i in range(rank,len(a)) if a[i][col]),None)
        if chosen is None:continue
        a[rank],a[chosen]=a[chosen],a[rank]
        inv=pow(a[rank][col],-1,q)
        a[rank]=[x*inv%q for x in a[rank]]
        for i in range(len(a)):
            if i!=rank and a[i][col]:
                scale=a[i][col]
                a[i]=[(x-scale*y)%q for x,y in zip(a[i],a[rank])]
        pivots.append(col)
        if len(pivots)==len(a):break
    free=[j for j in range(n) if j not in pivots]
    coefficients=[[-a[i][j]%q for j in free] for i in range(len(pivots))]
    candidates=[]
    for tail in product((-1,1),repeat=len(free)-1):
        values=(1,)+tail
        solved=[]
        for coeff in coefficients:
            residue=sum(x*y for x,y in zip(coeff,values))%q
            if residue not in (1,q-1):break
            solved.append(1 if residue==1 else -1)
        else:
            vector=[0]*n
            for j,x in zip(free,values):vector[j]=x
            for j,x in zip(pivots,solved):vector[j]=x
            if vector[0]<0:vector=[-x for x in vector]
            assert all(dot(row,vector)%q==0 for row in original)
            candidates.append(vector)
    energies=Counter(sum(dot(row,v)**2 for row in original) for v in candidates)
    total=sum(energies.values())
    energy_sum=sum(e*c for e,c in energies.items())
    # Normalization up to sign does not affect the norm-lifting bound.
    assert all(e==0 or e>=4*q*q for e in energies)
    assert energies.get(0,0)*4*q*q >= total*4*q*q-energy_sum
    near_pairs=[(a,b) for a,b in combinations(range(n),2)
                if abs(sum(row[a]*row[b] for row in original))==len(original)-2]
    if n==4*(q+1) and len(original)*q*q>4*(q+1)**2:
        assert total==energies.get(0,0)+len(near_pairs)
        assert all(energy in (0,(n-4)**2) for energy in energies)
    return {'prime':q,'rank_mod_prime':len(pivots),
            'normalized_information_assignments':2**(len(free)-1),
            'modular_sign_classes':total,'energy_distribution':dict(sorted(energies.items())),
            'energy_sum':energy_sum,'exact_sign_classes':energies.get(0,0),
            'first_moment_lower_bound_numerator':total*4*q*q-energy_sum,
            'first_moment_lower_bound_denominator':4*q*q,
            'near_parallel_column_pair_count':len(near_pairs),
            'max_absolute_column_correlation':max(abs(sum(row[a]*row[b] for row in original))
                                                   for a,b in combinations(range(n),2)),
            'candidate_masks':[sum((x<0)<<j for j,x in enumerate(v)) for v in candidates]}


if __name__=='__main__':
    cases=[]
    for label,masks in [('terminal12',MASKS12),('terminal16rho3',MASKS16),
                        ('delete0',MASKS12[1:]),('delete1',MASKS12[:1]+MASKS12[2:])]:
        profiles=[modular_pool(masks,q) for q in (3,5,7)]
        case={'label':label,'row_masks':masks,'profiles':profiles}
        cases.append(case)
        print(label,[(v['prime'],v['rank_mod_prime'],v['modular_sign_classes'],
                      v['exact_sign_classes'],v['energy_distribution']) for v in profiles])
    # A deliberately nonzero correction term in the lifting theorem.
    masks16small=[sum((((i&j).bit_count()%2)==1)<<j for j in range(16))
                  for i in (0,1,2,3,4,5,6,8)]
    example=modular_pool(masks16small,3,16)
    assert example['near_parallel_column_pair_count']>0
    # Independent group-algebra coefficient computation on the nonzero example.
    small_rows=rows(masks16small,16)
    state={(0,)*8:1}
    for column in zip(*small_rows):
        updated=Counter()
        for residue,count in state.items():
            for sign in (-1,1):
                target=tuple((x+sign*y)%3 for x,y in zip(residue,column))
                updated[target]+=count
        state=updated
    coefficient=state.get((0,)*8,0)
    assert coefficient==2*example['modular_sign_classes']==88
    assert coefficient//2-example['near_parallel_column_pair_count']==36
    example['independent_group_algebra_identity_coefficient']=coefficient
    cases.append({'label':'order16_nonzero_correction','row_masks':masks16small,
                  'order':16,'profiles':[example]})
    print('order16 correction',example['modular_sign_classes'],example['exact_sign_classes'],
          example['near_parallel_column_pair_count'])
    (HERE/'checks.json').write_text(json.dumps({'status':'passed','profiles':cases},indent=2)+'\n',encoding='utf-8')
