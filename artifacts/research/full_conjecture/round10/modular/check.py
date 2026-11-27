"""Exact modular lifting at orders4mod8; independently written stdlib code."""
from itertools import product,combinations
from collections import Counter
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def transpose(a):return list(map(list,zip(*a)))
def mm(a,b):return [[dot(row,col) for col in zip(*b)] for row in a]


def gram(rows):
    n=len(rows[0])
    assert all(x in (-1,1) for row in rows for x in row)
    assert all(dot(row,row)==n for row in rows)
    assert all(dot(a,b)==0 for a,b in combinations(rows,2))


def paley(p):
    squares={x*x%p for x in range(1,p)}
    h=[[1]*(p+1)]
    for a in range(p):
        h.append([-1]+[1 if a==b or (a-b)%p in squares else -1 for b in range(p)])
    gram(h)
    return h


def conference_hadamard(p):
    squares={x*x%p for x in range(1,p)}
    c=[[0]*(p+1) for _ in range(p+1)]
    for i in range(1,p+1):c[0][i]=c[i][0]=1
    for a in range(p):
        for b in range(p):
            if a!=b:c[a+1][b+1]=1 if (a-b)%p in squares else -1
    assert mm(c,c)==[[p*int(i==j) for j in range(p+1)] for i in range(p+1)]
    h=[]
    for i in range(p+1):
        h.append([c[i][j]+int(i==j) for j in range(p+1)]+[c[i][j]-int(i==j) for j in range(p+1)])
    for i in range(p+1):
        h.append([c[i][j]-int(i==j) for j in range(p+1)]+[-c[i][j]-int(i==j) for j in range(p+1)])
    gram(h)
    return h


def key(v):
    if v[0]<0:v=[-x for x in v]
    return tuple(v)


def modular_classes(rows,q):
    n=len(rows[0])
    a=[[x%q for x in row] for row in rows]
    pivots=[]
    for j in range(n):
        r=len(pivots)
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        inv=pow(a[r][j],-1,q)
        a[r]=[x*inv%q for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                scale=a[i][j]
                a[i]=[(x-scale*y)%q for x,y in zip(a[i],a[r])]
        pivots.append(j)
        if len(pivots)==len(a):break
    free=[j for j in range(n) if j not in pivots]
    coefficients=[[-a[i][j]%q for j in free] for i in range(len(pivots))]
    answer=[]
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
            assert all(dot(row,vector)%q==0 for row in rows)
            answer.append(key(vector))
    return answer,len(pivots),2**(len(free)-1)


def profile(rows,q,label):
    n=len(rows[0]);r=len(rows)
    gram(rows)
    candidates,rank,assignments=modular_classes(rows,q)
    exact=[v for v in candidates if all(dot(row,v)==0 for row in rows)]
    nonexact=[v for v in candidates if v not in exact]
    original={key(row) for row in rows}
    closed=len(rows)==4 and len({row[0]*row[1]*row[2]*row[3] for row in zip(*rows)})==1
    correction=r+(4 if closed else 0)
    assert len(exact)==len(candidates)-correction
    if r>=5:
        assert set(nonexact)==original
        assert rank<=n//2
    return {'label':label,'order':n,'q':q,'rows':r,'rank_mod_q':rank,
            'information_assignments':assignments,'modular_classes':len(candidates),
            'exact_extensions':len(exact),'correction':correction,'closed_quadruple':closed}


if __name__=='__main__':
    reports=[]
    matrices=[(3,paley(11)),(5,paley(19)),(7,conference_hadamard(13))]
    for q,h in matrices:
        n=len(h)
        for r in (n//2,n-2,n):
            reports.append(profile(h[:r],q,f'H{n} first{r}rows'))
    h4=[[1-2*((i&j).bit_count()%2) for j in range(4)] for i in range(4)]
    for q in (3,5):
        repeated=[[x for x in row for _ in range(q)] for row in h4]
        reports.append(profile(repeated,q,f'closedquad repeated{q}'))
    h12=matrices[0][1]
    reports.append(profile(h12[:4],3,'nonclosed quadruple H12'))
    # Small independent finite group-algebra count for the positivity formula.
    p=h12[:5]
    special=profile(p,3,'H12 first5rows')
    state={(0,)*5:1}
    for column in zip(*p):
        out=Counter()
        for residue,count in state.items():
            for sign in (-1,1):out[tuple((x+sign*y)%3 for x,y in zip(residue,column))]+=count
        state=out
    coefficient=state[(0,)*5]
    assert coefficient//2-5==special['exact_extensions']
    special['group_algebra_constant_coefficient']=coefficient
    reports.append(special)
    output={'status':'passed','arithmetic':'exact integer','profiles':reports,
            'scope':'Finite checks support the proof for arbitrary odd q; Gaussian enumeration uses prime q.'}
    (HERE/'checks.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(output,indent=2))
