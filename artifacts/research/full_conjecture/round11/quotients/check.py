"""Exact hyperbolic quotient grids and optimal compatible sign frames."""
from itertools import product,combinations
from pathlib import Path
from collections import Counter
import json

HERE=Path(__file__).resolve().parent
P=5
C=[[1,0,0,0,0,0,0,0,0,0,3,2,2,4,4,0,0,1,3,0],
 [0,1,0,0,0,0,0,0,0,0,4,3,0,1,0,1,4,0,1,0],
 [0,0,1,0,0,0,0,0,0,0,1,2,3,0,3,1,1,0,0,3],
 [0,0,0,1,0,0,0,0,0,0,2,4,4,0,2,4,2,1,3,2],
 [0,0,0,0,1,0,0,0,0,0,1,2,0,3,3,4,2,4,0,0],
 [0,0,0,0,0,1,0,0,0,0,0,3,3,1,0,0,4,2,4,2],
 [0,0,0,0,0,0,1,0,0,0,2,2,0,0,0,1,4,3,4,3],
 [0,0,0,0,0,0,0,1,0,0,0,2,2,2,1,1,3,3,4,1],
 [0,0,0,0,0,0,0,0,1,0,0,4,1,3,2,2,3,2,1,1],
 [0,0,0,0,0,0,0,0,0,1,3,2,1,2,1,2,3,0,1,4]]


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def rref(rows,p=P):
    a=[[x%p for x in row] for row in rows];k=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(k,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[k],a[pivot]=a[pivot],a[k]
        inv=pow(a[k][j],-1,p);a[k]=[x*inv%p for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                scale=a[i][j];a[i]=[(x-scale*y)%p for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return a[:k]


def kernel(rows,p=P):
    a=rref(rows,p);n=len(a[0]);piv=[next(j for j,x in enumerate(row) if x) for row in a]
    answer=[]
    for j in range(n):
        if j in piv:continue
        v=[0]*n;v[j]=1
        for row,i in zip(a,piv):v[i]=-row[j]%p
        answer.append(v)
    return answer


def solve(rows,rhs,p=P):
    a=rref([row+[b] for row,b in zip(rows,rhs)],p)
    answer=[0]*len(rows[0])
    for row in a:
        pivot=next(j for j,x in enumerate(row[:-1]) if x)
        answer[pivot]=row[-1]
    assert all(dot(row,answer)%p==b%p for row,b in zip(rows,rhs))
    return answer


def signs(basis,p=P):
    basis=rref(basis,p);answer=[]
    assert basis[0][0]==1
    for tail in product((1,p-1),repeat=len(basis)-1):
        coefficients=(1,)+tail
        v=[sum(x*row[j] for x,row in zip(coefficients,basis))%p for j in range(len(basis[0]))]
        if all(x in (1,p-1) for x in v):answer.append(tuple(1 if x==1 else -1 for x in v))
    return sorted(answer)


def normalize(v,p=P):
    lead=next(x for x in v if x%p)
    inv=pow(lead%p,-1,p)
    return tuple(x*inv%p for x in v)


def grid_label(v,e,f,p=P):
    x=[dot(v,w)%p for w in f];y=[dot(v,w)%p for w in e]
    a=((x[0],x[1]),(-y[1]%p,y[0]))
    assert (a[0][0]*a[1][1]-a[0][1]*a[1][0])%p==0
    if not any(x+y):return None
    column=next((a[0][j],a[1][j]) for j in range(2) if a[0][j] or a[1][j])
    u=normalize(column,p)
    i=next(i for i,x in enumerate(u) if x)
    z=normalize([a[i][j]*pow(u[i],-1,p)%p for j in range(2)],p)
    return u,z


def experiment(indices,label):
    old=signs(C);retained=[old[i] for i in indices];g=rref(retained)
    assert len(g)==8 and len(retained)>=5
    current=g[:];e=[]
    for row in C:
        if len(rref(current+[row]))>len(current):
            e.append(row);current=rref(current+[row])
    assert len(e)==2
    raw=[solve(g+e,[0]*8+[int(i==j) for j in range(2)]) for i in range(2)]
    b=[[dot(a,z)%P for z in raw] for a in raw]
    inv2=pow(2,-1,P)
    f=[[(raw[i][j]-inv2*sum(b[i][k]*e[k][j] for k in range(2)))%P for j in range(20)] for i in range(2)]
    assert all(dot(e[i],f[j])%P==int(i==j) for i in range(2) for j in range(2))
    assert all(dot(a,z)%P==0 for a in e for z in e)
    assert all(dot(a,z)%P==0 for a in f for z in f)
    assert all(dot(a,z)%P==0 for a in g for z in e+f)
    pool=signs(kernel(g));common=signs(g)
    labels={v:grid_label(v,e,f) for v in pool}
    assert {v for v,l in labels.items() if l is None}==set(common)
    points=[(1,a) for a in range(P)]+[(0,1)]
    weights=[[sum(l==(a,z) for l in labels.values()) for z in points] for a in points]
    row_sums=list(map(sum,weights));col_sums=list(map(sum,zip(*weights)))
    for a,z in combinations(pool,2):
        left,right=labels[a],labels[z]
        compatible=(left is None or right is None or left[0]==right[0] or left[1]==right[1])
        assert (dot(a,z)==0)==compatible
    extensions=[]
    for ruling in ('row','column'):
        for i,point in enumerate(points):
            u,v=point
            if ruling=='row':
                extra=[[u*e[0][j]-v*f[1][j] for j in range(20)],
                       [u*e[1][j]+v*f[0][j] for j in range(20)]]
            else:
                extra=[[u*e[0][j]+v*e[1][j] for j in range(20)],
                       [v*f[0][j]-u*f[1][j] for j in range(20)]]
            code=rref(g+extra)
            assert len(code)==10 and all(dot(a,z)%P==0 for a in code for z in code)
            family=signs(code)
            predicted=len(common)+(row_sums if ruling=='row' else col_sums)[i]
            assert len(family)==predicted
            assert set(retained)<=set(family)
            assert all(dot(a,z)==0 for a,z in combinations(family,2))
            overlap=set(old)&set(family)
            extensions.append({'ruling':ruling,'point':point,'sign_count':len(family),
                               'sign_span_rank':len(rref(family)),
                               'original_classes_retained':len(overlap),
                               'deleted_original_sorted_indices':[i for i,v in enumerate(old) if v not in overlap],
                               'basis':code,'sign_masks':[sum((x<0)<<j for j,x in enumerate(v)) for v in family]})
    assert sum(x['sign_count'] for x in extensions)==2*len(pool)+2*P*len(common)
    best=max(x['sign_count'] for x in extensions)
    assert all(len(rref([v for j,v in enumerate(old) if j!=i]))==10 for i in range(12))
    minimum_full=min(12-x['original_classes_retained'] for x in extensions if x['sign_count']==20)
    assert minimum_full==2
    square_weights=sum(x*x for row in weights for x in row)
    ordered_pairs=sum(x*x for x in row_sums+col_sums)-2*square_weights
    return {'label':label,'retained_indices':indices,'retained_rows':len(retained),'rank':len(g),
            'index_convention':'lexicographically sorted normalized sign representatives of embedded C',
            'original_sorted_sign_masks':[sum((x<0)<<j for j,x in enumerate(v)) for v in old],
            'retained_space_basis':g,'hyperbolic_quotient_lifts':{'e':e,'f':f},
            'pool_sign_masks_and_grid_labels':[{'mask':sum((x<0)<<j for j,x in enumerate(v)),
                                                 'grid_label':labels[v]} for v in pool],
            'common_sign_classes':len(common),'modular_pool':len(pool),'grid_points':points,
            'weights':weights,'row_sums':row_sums,'column_sums':col_sums,
            'exact_maximum_compatible_frame':best,'extensions':extensions,
            'minimum_full_repair_deletions':minimum_full,
            'all_single_deletion_spans_have_rank10':True,
            'occupied_grid_points':sum(x>0 for row in weights for x in row),
            'squared_point_weights':square_weights,'ordered_distinct_point_orthogonal_weight':ordered_pairs,
            'average_lower_bound':len(common)+(len(pool)-len(common)+P)//(P+1)}


if __name__=='__main__':
    assert len(C)==10 and all(dot(a,b)%P==0 for a in C for b in C)
    old=signs(C);assert len(old)==12
    independent=[]
    for i,row in enumerate(old):
        if len(rref([old[j] for j in independent]+[row]))>len(independent):independent.append(i)
        if len(independent)==8:break
    report=experiment(independent,'greedy rank8 retained subframe')
    second=experiment(list(range(11,3,-1)),'original trap JSON literal first8')
    assert second['common_sign_classes']==9 and second['modular_pool']==51
    assert second['squared_point_weights']==96 and second['ordered_distinct_point_orthogonal_weight']==588
    (HERE/'checks.json').write_text(json.dumps({'status':'passed','p':P,'source_code_basis':C,
        'experiments':[report,second]},indent=2)+'\n',encoding='utf-8')
    for item in (report,second):
        print(json.dumps({k:item[k] for k in ('label','common_sign_classes','modular_pool',
              'exact_maximum_compatible_frame','minimum_full_repair_deletions','row_sums','column_sums')}))
