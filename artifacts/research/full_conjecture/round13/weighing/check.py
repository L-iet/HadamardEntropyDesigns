"""Exact eight-state weighing completion certificates; stdlib only."""
from itertools import product,combinations
from pathlib import Path
from fractions import Fraction
import json

HERE=Path(__file__).resolve().parent
H2=[[1,1],[1,-1]]
BAD=[[0,0,1,1,1,1,1,1,1,1,1,1],
 [0,0,1,-1,-1,1,-1,1,-1,1,-1,1],
 [1,-1,0,0,-1,-1,-1,-1,1,1,1,1],
 [1,1,0,0,-1,1,-1,1,1,-1,1,-1],
 [1,-1,-1,-1,0,0,1,1,-1,-1,1,1],
 [1,1,1,-1,0,0,1,-1,1,-1,-1,1],
 [1,-1,-1,-1,1,1,0,0,1,1,-1,-1],
 [1,1,1,-1,1,-1,0,0,-1,1,1,-1],
 [1,-1,1,1,-1,-1,1,1,0,0,-1,-1],
 [1,1,-1,1,1,-1,-1,1,0,0,-1,1],
 [1,-1,1,1,1,1,-1,-1,-1,-1,0,0],
 [1,1,-1,1,-1,1,1,-1,-1,1,0,0]]


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def tr(a):return list(map(list,zip(*a)))
def mm(a,b):return [[dot(row,col) for col in zip(*b)] for row in a]
def neg(a):return [[-x for x in row] for row in a]
def plus(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def block(a,i,j):return [row[2*j:2*j+2] for row in a[2*i:2*i+2]]
def tensor(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def eye(n,k=1):return [[k*int(i==j) for j in range(n)] for i in range(n)]


def group():
    return [[[a,0],[0,b]] for a,b in product((-1,1),repeat=2)]+[
        [[0,a],[b,0]] for a,b in product((-1,1),repeat=2)]


def eight_test(w):
    n=len(w);m=n//2
    assert mm(w,tr(w))==eye(n,n-2)
    assert all((w[i][j]==0)==(i//2==j//2) for i in range(n) for j in range(n))
    a={}
    for i in range(m):
        for j in range(m):
            if i==j:continue
            raw=mm(block(w,i,j),H2)
            assert all(x%2==0 for row in raw for x in row)
            a[i,j]=[[x//2 for x in row] for row in raw]
            assert a[i,j] in group()
    accepted=[];rejected=[]
    for root in group():
        states=[root]+[neg(mm(mm(a[j,0],tr(root)),a[0,j])) for j in range(1,m)]
        assert all(s in group() for s in states)
        failure=None
        for i,j in combinations(range(m),2):
            residual=plus(mm(a[i,j],tr(states[j])),mm(states[i],tr(a[j,i])))
            if residual!=[[0,0],[0,0]]:
                failure={'pair':[i,j],'residual':residual};break
        if failure:
            rejected.append({'root':root,'failure':failure})
        else:
            fill=[[0]*n for _ in range(n)]
            for i,state in enumerate(states):
                small=mm(state,H2)
                for r in range(2):
                    for c in range(2):fill[2*i+r][2*i+c]=small[r][c]
            h=plus(w,fill)
            assert all(abs(x)==1 for row in h for x in row)
            assert mm(h,tr(h))==eye(n,n)
            accepted.append({'root':root,'states':states,'filled_hadamard':h})
    return {'order':n,'weighing_weight':n-2,'accepted_roots':accepted,'rejected_roots':rejected,
            'zero_preserving_completions':len(accepted)}


def conference(p):
    residues={x*x%p for x in range(1,p)}
    eps=1 if p%4==1 else -1
    c=[[0]+[1]*p]
    for i in range(p):
        c.append([eps]+[0 if i==j else (1 if (i-j)%p in residues else -1) for j in range(p)])
    assert mm(c,tr(c))==eye(p+1,p)
    return c


def diagonal_fills(c):
    n=len(c)
    signs=[1]+[-c[0][j]*c[j][0] for j in range(1,n)]
    valid=all(c[i][j]*signs[j]+signs[i]*c[j][i]==0 for i,j in combinations(range(n),2))
    if valid:
        for overall in (-1,1):
            h=[row[:] for row in c]
            for i in range(n):h[i][i]=overall*signs[i]
            assert mm(h,tr(h))==eye(n,n)
    return 2 if valid else 0


def rank(rows):
    a=[list(map(Fraction,row)) for row in rows];r=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        scale=a[r][j];a[r]=[x/scale for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                scale=a[i][j];a[i]=[x-scale*y for x,y in zip(a[i],a[r])]
        r+=1
    return r


if __name__=='__main__':
    bad=eight_test(BAD)
    assert bad['zero_preserving_completions']==0 and len(bad['rejected_roots'])==8
    identity=eye(2);d=[[1,0],[0,-1]];s=[[0,1],[1,0]];j=mm(d,s)
    bases=[[[int(r==i and c==k) for c in range(2)] for r in range(2)]
           for i in range(2) for k in range(2)]
    coefficient_columns=[]
    for root in bases:
        first=plus(root,mm(mm(j,tr(root)),j))
        second=plus(mm(root,s),mm(s,tr(root)))
        coefficient_columns.append([x for a in (first,second) for row in a for x in row])
    linear_constraints=tr(coefficient_columns)
    assert rank(linear_constraints)==4
    symbols={'0':[[0,0],[0,0]],'I':identity,'D':d,'S':s,'J':j}
    symbols.update({'-'+key:neg(value) for key,value in list(symbols.items()) if key!='0'})
    table=[['0','I','D','D','D','D'],['S','0','-I','-I','I','I'],
           ['S','-D','0','I','-D','D'],['S','-D','I','0','D','-D'],
           ['S','D','-D','D','0','-I'],['S','D','D','-D','-I','0']]
    full_a=[[x for name in names for x in symbols[name][r]] for names in table for r in range(2)]
    assert mm(full_a,tr(full_a))==eye(12,5)
    assert mm(full_a,tensor(eye(6),H2))==BAD
    skew4=conference(3);symmetric6=conference(5)
    assert diagonal_fills(skew4)==2 and diagonal_fills(symmetric6)==0
    small=eight_test(tensor([[0,1],[-1,0]],H2))
    skew=eight_test(tensor(skew4,H2))
    symmetric=eight_test(tensor(symmetric6,H2))
    assert [small['zero_preserving_completions'],skew['zero_preserving_completions'],
            symmetric['zero_preserving_completions']]==[8,6,2]
    # Invariance under a nontrivial signing, preserving the zero pattern.
    changed=[[BAD[i][j]*(-1 if i%3==0 else 1)*(-1 if j%4==0 else 1)
              for j in range(12)] for i in range(12)]
    assert eight_test(changed)['zero_preserving_completions']==0
    result={'status':'passed','arithmetic':'exact integer/rational','counterexample':{'matrix':BAD,**bad,
              'block_symbols':table,'real_triangle_constraint_matrix':linear_constraints,
              'real_triangle_constraint_rank':4,'no_real_zero_supported_completion':True},
            'positive_examples':[small,skew,symmetric],
            'conference_diagonal_fill_counts':{'skew_order4':2,'symmetric_order6':0},
            'scope':'Near-full weighing matrices do not automatically admit zero-preserving Hadamard filling.'}
    (HERE/'checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','unfillable_weighing_order':12,'weight':10,
                      'root_failure_certificates':8,'positive_fill_counts':[8,6,2]}))
