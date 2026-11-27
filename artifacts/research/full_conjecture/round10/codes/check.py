# SPDX-License-Identifier: Apache-2.0
"""Exact restricted-alphabet code checks; no external packages or source."""
from pathlib import Path
from itertools import product
import importlib.util
import json
import random

ROOT = Path(__file__).resolve().parent

def dot(a,b): return sum(x*y for x,y in zip(a,b))

def rref(rows,p):
    a=[list(x) for x in rows];k=0
    for col in range(len(a[0])):
        hit=next((i for i in range(k,len(a)) if a[i][col]%p),None)
        if hit is None: continue
        a[k],a[hit]=a[hit],a[k]
        scale=pow(a[k][col]%p,-1,p);a[k]=[x*scale%p for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                scale=a[i][col]%p
                a[i]=[(x-scale*y)%p for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a): break
    return tuple(tuple(x) for x in a[:k])

def span(basis,p):
    n=len(basis[0])
    return {tuple(sum(c*x[j] for c,x in zip(coeff,basis))%p for j in range(n))
            for coeff in product(range(p),repeat=len(basis))}

def kernel(rows,p):
    reduced=rref(rows,p);n=len(rows[0])
    piv=[next(i for i,x in enumerate(row) if x) for row in reduced]
    basis=[]
    for j in range(n):
        if j in piv: continue
        v=[0]*n;v[j]=1
        for row,k in zip(reduced,piv): v[k]=-row[j]%p
        basis.append(tuple(v))
    return basis

def signs(words,p):
    return sorted({tuple(1 if x==1 else -1 for x in w) for w in words
                   if all(x in (1,p-1) for x in w) and w[0]==1})

def sign_words_from_systematic(basis,p):
    """RREF pivots equal the coefficients; enumerate only sign coefficients."""
    out=[]
    for tail in product((1,p-1),repeat=len(basis)-1):
        coeff=(1,)+tail
        word=tuple(sum(c*row[j] for c,row in zip(coeff,basis))%p
                   for j in range(len(basis[0])))
        if all(x in (1,p-1) for x in word):
            out.append(tuple(1 if x==1 else -1 for x in word))
    return out

def self_dual_extension(seed,p,rng):
    basis=rref(seed,p);n=len(seed[0])
    while len(basis)<n//2:
        dual=kernel(basis,p)
        for attempt in range(10000):
            coeff=[rng.randrange(p) for _ in dual]
            v=tuple(sum(c*row[j] for c,row in zip(coeff,dual))%p for j in range(n))
            if dot(v,v)%p:continue
            larger=rref(basis+(v,),p)
            if len(larger)>len(basis):
                basis=larger;break
        else:raise AssertionError('extension search exhausted')
    return basis

def pivot_code(basis,v,p):
    alpha=[dot(row,v)%p for row in basis]
    assert any(alpha)
    coeff_basis=kernel([alpha],p)
    kept=[tuple(sum(c*row[j] for c,row in zip(coeff,basis))%p
                for j in range(len(v))) for coeff in coeff_basis]
    out=rref(kept+[tuple(x%p for x in v)],p)
    assert len(out)==len(basis)
    assert all(dot(a,b)%p==0 for a in out for b in out)
    return out

def verify_family(rows,q):
    n=4*q
    assert len(set(rows))==len(rows) and all(x[0]==1 for x in rows)
    assert all(dot(a,b)%q==0 for a in rows for b in rows)
    parity={s:[] for s in (-1,1)}
    for row in rows:
        prod=1
        for x in row: prod*=x
        parity[prod].append(row)
    for group in parity.values():
        assert all(dot(a,b)==n*(a==b) for a in group for b in group)
    if all(parity.values()):
        assert all(len(g)<=4 for g in parity.values())
        assert all(abs(dot(a,b))==n//2 for a in parity[1] for b in parity[-1])
    assert len(rows)<=n
    return sorted(len(g) for g in parity.values())

def main():
    spec=importlib.util.spec_from_file_location('known_paley',ROOT.parents[1]/'round9/check_rank.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    h=module.paley_two(5)
    seed=h[:5];p=3
    base=rref(seed,p);words=span(base,p)
    null=span(kernel(seed,p),p)
    completions=set()
    if len(base)==6: completions.add(base)
    else:
        assert len(base)==5
        for v in null-words:
            if dot(v,v)%p==0: completions.add(rref(base+(v,),p))
    records=[]
    for basis in sorted(completions):
        assert len(basis)==6
        assert all(dot(a,b)%p==0 for a in basis for b in basis)
        candidate=signs(span(basis,p),p)
        assert all(tuple(row if row[0]==1 else [-x for x in row]) in candidate for row in seed)
        split=verify_family(candidate,p)
        assert len(candidate)>=5 and 0 in split
        records.append({'selfDualBasis':[list(x) for x in basis],
                        'signClasses':len(candidate),'parityClassSizes':split})
    assert len(records)==2 and all(x['signClasses']==12 for x in records)
    # A self-dual ternary code can contain no sign word at all.
    tetra=((1,0,1,1),(0,1,1,2))
    tetrabasis=[]
    for start in (0,4,8):
        for row in tetra:
            v=[0]*12;v[start:start+4]=row;tetrabasis.append(v)
    assert all(dot(a,b)%3==0 for a in tetrabasis for b in tetrabasis)
    assert len(rref(tetrabasis,3))==6
    assert not signs(span(tetrabasis,3),3)
    # Sharp mixed-parity example, valid for composite as well as prime q.
    h4=((1,1,1,1),(1,-1,1,-1),(1,1,-1,-1),(1,-1,-1,1))
    mixed=[]
    for coeff in product((-1,1),repeat=4):
        values=[sum(c*row[j] for c,row in zip(coeff,h4)) for j in range(4)]
        if all(abs(x)==2 for x in values):
            row=tuple(x//2 for x in values)
            if row[0]==1:mixed.append(row)
    examples=[]
    for q in (3,5,9):
        family=[tuple(x for x in row for _ in range(q)) for row in list(h4)+mixed]
        assert len(family)==8
        split=verify_family(family,q);assert split==[4,4]
        examples.append({'q':q,'classes':len(family),'parityClassSizes':split})
    result={'passed':True,'order12FiveRowSeedRank':len(base),
            'allSelfDualExtensionsOfSeed':records,
            'selfDualTetracodeSumSignClasses':0,'sharpMixedFamilies':examples,
            'scope':'Known-order examples and finite-field enumeration, not unknown-order existence.'}
    # Independently generated known H20; find a bad choice of self-dual
    # extension, rather than assuming that every completion has many signs.
    q=19;residues={x*x%q for x in range(1,q)}
    chi=lambda x:0 if x%q==0 else (1 if x%q in residues else -1)
    h20=[[1]*20]+[[1]+[chi(j-i)-(i==j) for j in range(q)] for i in range(q)]
    assert all(dot(a,b)==20*(i==j) for i,a in enumerate(h20) for j,b in enumerate(h20))
    rng=random.Random(20261120);profiles=[];bad=None
    for trial in range(40):
        basis=self_dual_extension(h20[:5],5,rng)
        assert len(basis)==10 and all(dot(a,b)%5==0 for a in basis for b in basis)
        family=sign_words_from_systematic(basis,5)
        verify_family(family,5);assert len(family)>=5
        profiles.append(len(family))
        if len(family)<20:
            bad={'basis':[list(x) for x in basis],'signClasses':len(family),
                 'signRepresentatives':[list(x) for x in family]}
            break
    assert bad is not None
    family=[tuple(row) for row in bad['signRepresentatives']]
    candidates=sign_words_from_systematic(rref(kernel(family,5),5),5)
    exact=[v for v in candidates if all(dot(v,row)==0 for row in family)]
    assert len(candidates)==len(family)+len(exact)
    bad['frameRankMod5']=len(rref(family,5))
    bad['frameModularCandidates']=len(candidates)
    bad['frameExactExtensions']=len(exact)
    bad['exactExtensionWitness']=list(exact[0]) if exact else None
    current=tuple(tuple(row) for row in bad['basis'])
    walk=[len(family)]
    while len(family)<20:
        candidates=sign_words_from_systematic(rref(kernel(family,5),5),5)
        exact=[v for v in candidates if all(dot(v,row)==0 for row in family)]
        if not exact:break
        current=pivot_code(current,exact[0],5)
        larger=sign_words_from_systematic(current,5)
        assert set(family)<set(larger)
        family=larger;verify_family(family,5);walk.append(len(family))
    bad['monotoneCodePivotSignCounts']=walk
    bad['finalCodeBasis']=[list(row) for row in current]
    assert bad['signClasses']==8
    assert bad['frameModularCandidates']==40 and bad['frameExactExtensions']==32
    assert walk==[8,20]
    result['order20SelfDualExtensionProfiles']=profiles
    result['order20InsufficientSelfDualExtension']=bad
    (ROOT/'checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Restricted-alphabet code checks passed:',[x['signClasses'] for x in records])

if __name__=='__main__':main()
