"""Exact finite concatenation checks; these do not test or prove GRH."""
from functools import lru_cache
from itertools import combinations
from math import isqrt
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def gram(rows,order):
    assert all(len(row)==order and all(x in (-1,1) for x in row) for row in rows)
    assert all(dot(row,row)==order for row in rows)
    assert all(dot(a,b)==0 for a,b in combinations(rows,2))


def tensor(a,b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


@lru_cache(None)
def sylvester(n):
    assert n>0 and n&(n-1)==0
    return [[1-2*((i&j).bit_count()%2) for j in range(n)] for i in range(n)]


@lru_cache(None)
def paley(p):
    assert prime(p) and p%4==3
    residues={x*x%p for x in range(1,p)}
    h=[[1]*(p+1)]
    for i in range(p):
        h.append([-1]+[1 if i==j or (i-j)%p in residues else -1 for j in range(p)])
    gram(h,p+1)
    return h


@lru_cache(None)
def conference_hadamard(p):
    assert prime(p) and p%4==1
    residues={x*x%p for x in range(1,p)}
    c=[[0]*(p+1) for _ in range(p+1)]
    for j in range(1,p+1):c[0][j]=c[j][0]=1
    for i in range(p):
        for j in range(p):
            if i!=j:c[i+1][j+1]=1 if (i-j)%p in residues else -1
    assert all(dot(a,b)==p*int(i==j) for i,a in enumerate(c) for j,b in enumerate(c))
    h=[]
    for i in range(p+1):
        h.append([c[i][j]+int(i==j) for j in range(p+1)]+[c[i][j]-int(i==j) for j in range(p+1)])
    for i in range(p+1):
        h.append([c[i][j]-int(i==j) for j in range(p+1)]+[-c[i][j]-int(i==j) for j in range(p+1)])
    gram(h,2*(p+1))
    return h


@lru_cache(None)
def buffer_block(order):
    odd=order;twos=0
    while odd%2==0:odd//=2;twos+=1
    if odd==1:return sylvester(order)
    bases={3:lambda:paley(11),5:lambda:paley(19),
           7:lambda:conference_hadamard(13),9:lambda:conference_hadamard(17)}
    assert odd in bases and twos>=2
    return tensor(bases[odd](),sylvester(2**(twos-2)))


if __name__=='__main__':
    q=16
    targets=[96,112,128,144,160,164,168,172,176,180,192,208,224,240,256]
    records=[]
    for n in targets:
        x=n//2-1
        residue=(n-1)%q
        choices=[p for p in range(3,x+1) if p%q==residue and prime(p)]
        p=max(choices)
        b=p+1;a=n-b;k=a//q
        assert a==q*k and 1<=k<=n and p%4==3 and b<=n//2
        left=buffer_block(a);right=paley(p)
        rectangular=[ar+br for ar,br in zip(left[:b],right)]
        assert len(rectangular)==b
        gram(rectangular,n)
        records.append({'target':n,'buffer':q,'residue_n_minus1':residue,
                        'chosen_prime':p,'k':k,'left_hadamard_order':a,
                        'paley_order':b,'partial_rows':b,'half_deficit':n//2-b,
                        'full_integer_gram_verified':True})
    assert any(row['target']%q for row in records)
    assert any(row['residue_n_minus1']!=q-1 for row in records)
    output={'status':'passed','arithmetic':'exact integer','cases':records,
            'conditional_scope':'Finite examples are unconditional. GRH and asymptotic estimates are assumptions, not tested claims.',
            'buffer_scope':'Q16 here is a finite known-order test choice, not a numerical value for the asymptotic uniform buffer.'}
    (HERE/'checks.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','exact_concatenations':len(records),
                      'targets':[r['target'] for r in records],
                      'non_minus_one_residues':sorted({r['residue_n_minus1'] for r in records if r['residue_n_minus1']!=15})}))
