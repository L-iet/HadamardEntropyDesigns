"""Exact real-kernel and conference-converter checks; stdlib only."""
from itertools import product,combinations
from fractions import Fraction
from pathlib import Path
from collections import Counter
import json

HERE=Path(__file__).resolve().parent
I=[[1,0],[0,1]];J=[[0,1],[-1,0]];D=[[1,0],[0,-1]];S=[[0,1],[1,0]];F=[[1,1],[1,-1]]

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def tr(a):return list(map(list,zip(*a)))
def mm(a,b):return [[dot(row,col) for col in zip(*b)] for row in a]
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a):return [[-x for x in row] for row in a]
def eye(n,k=1):return [[k*int(i==j) for j in range(n)] for i in range(n)]
def tensor(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def block(a,i,j):return [row[2*j:2*j+2] for row in a[2*i:2*i+2]]
GROUP=[[[a,0],[0,b]] for a,b in product((-1,1),repeat=2)]+[[[0,a],[b,0]] for a,b in product((-1,1),repeat=2)]

def rank(a):
    a=[list(map(Fraction,row)) for row in a];r=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        scale=a[r][j];a[r]=[x/scale for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                scale=a[i][j];a[i]=[x-scale*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r

def data(w):
    n=len(w);m=n//2
    assert mm(w,tr(w))==eye(n,n-2)
    a={}
    for i,j in product(range(m),repeat=2):
        if i!=j:
            raw=mm(block(w,i,j),F)
            a[i,j]=[[x//2 for x in row] for row in raw]
            assert a[i,j] in GROUP
    return a

def states(a,root):
    m=1+max(i for i,j in a)
    return [root]+[neg(mm(mm(a[j,0],tr(root)),a[0,j])) for j in range(1,m)]

def residual(a,root):
    roots=states(a,root);answer=[]
    for i,j in combinations(range(len(roots)),2):
        value=add(mm(a[i,j],tr(roots[j])),mm(roots[i],tr(a[j,i])))
        answer.extend(x for row in value for x in row)
    return answer

def classify(a,bases):
    columns=[residual(a,b) for b in bases]
    matrix=tr(columns)
    dimension=2-rank(matrix)
    probes={'axis0':(1,0),'axis1':(0,1),'diagonal+':(1,1),'diagonal-':(1,-1)}
    valid=[name for name,(u,v) in probes.items() if all(u*x+v*y==0 for x,y in matrix)]
    assert (dimension==2 and len(valid)==4) or (dimension==1 and len(valid)==1) or (dimension==0 and not valid)
    return {'dimension':dimension,'kind':'plane' if dimension==2 else ('zero' if dimension==0 else valid[0]),
            'valid_probes':valid}

def fill_from_states(w,root_states,scale=1):
    n=len(w);x=[[0]*n for _ in range(n)]
    for i,root in enumerate(root_states):
        small=mm(root,F)
        assert all(v%scale==0 for row in small for v in row)
        for r,c in product(range(2),repeat=2):x[2*i+r][2*i+c]=small[r][c]//scale
    return x

def convert(w,diagonal_root):
    a=data(w)
    assert not any(residual(a,diagonal_root))
    t=fill_from_states(w,states(a,diagonal_root),2)
    n=len(w)
    assert mm(t,tr(t))==eye(n)
    assert all(w[i][j]*t[i][j]==0 for i in range(n) for j in range(n))
    c=mm(w,tr(t));assert c==neg(tr(c))
    u=add(c,eye(n));assert mm(u,tr(u))==eye(n,n-1)
    zero_columns=[next(j for j,x in enumerate(row) if x==0) for row in u]
    assert len(set(zero_columns))==n
    normalized=[[row[j] for j in zero_columns] for row in u]
    d=[1]+[-normalized[0][j]*normalized[j][0] for j in range(1,n)]
    y=[[0]*n for _ in range(n)]
    for i,j in enumerate(zero_columns):y[i][j]=d[i]
    assert y==neg(tr(y))
    outputs=[mm(add(u,sign_y),t) for sign_y in (y,neg(y))]
    roots=[]
    for filled in outputs:
        assert all(abs(x)==1 for row in filled for x in row)
        assert mm(filled,tr(filled))==eye(n,n)
        assert all(not w[i][j] or filled[i][j]==w[i][j] for i in range(n) for j in range(n))
        fill=add(filled,neg(w));raw=mm(block(fill,0,0),F)
        root=[[x//2 for x in row] for row in raw]
        assert root in GROUP and not any(residual(a,root))
        roots.append([x for row in root for x in row])
    assert rank(roots)==2
    return {'diagonal_root_sqrt2_scaled':diagonal_root,'monomial_t':t,
            'conference_zero_columns':zero_columns,'conference_fill_signs':d,
            'two_independent_sign_roots':roots,'two_hadamards':outputs}

def profile(w,label):
    a=data(w)
    rotation=classify(a,[I,J]);reflection=classify(a,[D,S])
    assert not rotation['kind'].startswith('diagonal') and not reflection['kind'].startswith('diagonal')
    sign_roots=[root for root in GROUP if not any(residual(a,root))]
    diagonal_roots=[add([[u*x for x in row] for row in left],[[v*x for x in row] for row in right])
                    for left,right in ((I,J),(D,S)) for u,v in product((-1,1),repeat=2)]
    diagonal_roots=[root for root in diagonal_roots if not any(residual(a,root))]
    converters=[convert(w,root) for root in diagonal_roots]
    if diagonal_roots:assert sign_roots
    for root in sign_roots:
        fill=fill_from_states(w,states(a,root))
        assert mm(add(w,fill),tr(add(w,fill)))==eye(len(w),len(w))
    assert len(sign_roots) in (0,2,4,6,8)
    if len(w)>=8:assert len(sign_roots)<=6
    return {'label':label,'order':len(w),'rotation':rotation,'reflection':reflection,
            'sign_fill_count':len(sign_roots),'diagonal_probe_count':len(diagonal_roots),
            'conference_converters':converters}

def conference(p):
    residues={x*x%p for x in range(1,p)};eps=1 if p%4==1 else -1
    return [[0]+[1]*p]+[[eps]+[0 if i==j else (1 if (i-j)%p in residues else -1) for j in range(p)] for i in range(p)]

def bounded_order8():
    n=8;pools=[]
    for i in range(n):
        support=[j for j in range(n) if j//2!=i//2]
        pool=[]
        for tail in product((-1,1),repeat=5):
            row=[0]*n
            for j,x in zip(support,(1,)+tail):row[j]=x
            pool.append(row)
        pools.append(pool)
    histogram=Counter();diagonal_line=None;count=0
    def dfs(rows):
        nonlocal count,diagonal_line
        if len(rows)==8:
            count+=1;a=data(rows);r=classify(a,[I,J]);s=classify(a,[D,S])
            key=(r['kind'],s['kind'],sum(not any(residual(a,x)) for x in GROUP))
            histogram[key]+=1
            if 'diagonal' in r['kind'] or 'diagonal' in s['kind']:diagonal_line=[row[:] for row in rows]
            return
        for row in pools[len(rows)]:
            if all(dot(row,old)==0 for old in rows):dfs(rows+[row])
    dfs([[0,0,1,1,1,1,1,1]])
    assert count==256
    return {'normalized_matrices':count,'component_histogram':[{'types':key,'count':value} for key,value in sorted(histogram.items())]},diagonal_line

if __name__=='__main__':
    symbols={'0':[[0,0],[0,0]],'I':I,'D':D,'S':S}
    symbols.update({'-'+k:neg(v) for k,v in list(symbols.items()) if k!='0'})
    table=[['0','I','D','D','D','D'],['S','0','-I','-I','I','I'],['S','-D','0','I','-D','D'],
           ['S','-D','I','0','D','-D'],['S','D','-D','D','0','-I'],['S','D','D','-D','-I','0']]
    a=[[x for name in names for x in symbols[name][r]] for names in table for r in range(2)]
    bad=mm(a,tensor(eye(6),F))
    profiles=[profile(tensor([[0,1],[-1,0]],F),'order4 full kernel'),
              profile(tensor(conference(3),F),'order8 skew conference'),
              profile(tensor(conference(5),F),'order12 symmetric conference'),
              profile(bad,'order12 inconsistent triangles')]
    # A genuinely nonsign rational completion lies in a full reflection circle.
    w=tensor(conference(3),F);a=data(w)
    rational_root=[[Fraction(3*x+4*y,5) for x,y in zip(ar,br)] for ar,br in zip(D,S)]
    assert not any(residual(a,rational_root))
    root_states=states(a,rational_root)
    fill=[[Fraction(0) for _ in range(8)] for _ in range(8)]
    for i,root in enumerate(root_states):
        small=mm(root,F)
        for r,c in product(range(2),repeat=2):fill[2*i+r][2*i+c]=small[r][c]
    rational_completion=add(w,fill)
    assert mm(rational_completion,tr(rational_completion))==eye(8,8)
    assert any(abs(x)!=1 for row in rational_completion for x in row)
    enumeration,isolated=bounded_order8()
    if isolated:profiles.append(profile(isolated,'order8 isolated diagonal line'))
    output={'status':'passed','arithmetic':'exact rational/integer','profiles':profiles,
            'nonsign_rational_completion':{'order':8,'root':[[str(x) for x in row] for row in rational_root],
                'matrix':[[str(x) for x in row] for row in rational_completion]},
            'bounded_order8_classification':enumeration,'isolated_diagonal_line_example':isolated}
    (HERE/'checks.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','profiles':[(p['label'],p['rotation']['kind'],p['reflection']['kind'],p['sign_fill_count']) for p in profiles],
                      'order8_classification':enumeration,'isolated_diagonal_example_found':isolated is not None}))
