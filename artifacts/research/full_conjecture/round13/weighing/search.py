"""New exact bounded search for zero-preserving weighing completions."""
from itertools import product
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def det2(a):return a[0][0]*a[1][1]-a[0][1]*a[1][0]
def block(w,i,j):return [row[2*j:2*j+2] for row in w[2*i:2*i+2]]
def tr(a):return list(map(list,zip(*a)))
def mm(a,b):return [[dot(row,col) for col in zip(*b)] for row in a]
STATES=[[[a,b],[c,-a*b*c]] for a,b,c in product((-1,1),repeat=3)]


def fillings(w):
    m=len(w)//2
    links={}
    for i in range(m):
        for j in range(i+1,m):
            a,b=block(w,i,j),block(w,j,i)
            pairs=set()
            for u,s in enumerate(STATES):
                for v,t in enumerate(STATES):
                    left,right=mm(a,tr(t)),mm(s,tr(b))
                    if all(x+y==0 for ar,br in zip(left,right) for x,y in zip(ar,br)):pairs.add((u,v))
            links[i,j]=pairs
    def dfs(chosen):
        if len(chosen)==m:return chosen
        j=len(chosen)
        for state in range(8):
            if all((s,state) in links[i,j] for i,s in enumerate(chosen)):
                out=dfs(chosen+[state])
                if out is not None:return out
        return None
    return dfs([])


def search(n=8,limit=10000):
    pools=[]
    for i in range(n):
        support=[j for j in range(n) if j//2!=i//2]
        candidates=[]
        for tail in product((-1,1),repeat=len(support)-1):
            row=[0]*n
            for j,x in zip(support,(1,)+tail):row[j]=x
            candidates.append(row)
        pools.append(candidates)
    first=[0,0]+[1]*(n-2)
    checked=0;hist={};result=None
    def dfs(rows):
        nonlocal checked,result
        if len(rows)==n:
            checked+=1
            solution=fillings(rows)
            hist[str(solution is not None)]=hist.get(str(solution is not None),0)+1
            if solution is None:
                result={'n':n,'weight':n-2,'matrix':rows,'checked':checked}
                return True
            return checked>=limit
        for row in pools[len(rows)]:
            if all(dot(row,old)==0 for old in rows):
                if dfs(rows+[row]):return True
        return False
    dfs([first])
    output={'checked':checked,'histogram':hist,'counterexample':result}
    (HERE/f'search{n}.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(output))


if __name__=='__main__':search()
