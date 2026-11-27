"""Exact reflection switch search and completion certificates; stdlib only."""
from itertools import product,combinations
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
I=[[1,0],[0,1]];D=[[1,0],[0,-1]];S=[[0,1],[1,0]];F=[[1,1],[1,-1]]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def tr(a):return list(map(list,zip(*a)))
def mm(a,b):return [[dot(row,col) for col in zip(*b)] for row in a]
def neg(a):return [[-x for x in row] for row in a]
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def eye(n,k=1):return [[k*int(i==j) for j in range(n)] for i in range(n)]
def tensor(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def block(a,i,j):return [row[2*j:2*j+2] for row in a[2*i:2*i+2]]
GROUP=[[[a,0],[0,b]] for a,b in product((-1,1),repeat=2)]+[[[0,a],[b,0]] for a,b in product((-1,1),repeat=2)]

def original():
    sym={'0':[[0,0],[0,0]],'I':I,'D':D,'S':S}
    sym.update({'-'+k:neg(v) for k,v in list(sym.items()) if k!='0'})
    table=[['0','I','D','D','D','D'],['S','0','-I','-I','I','I'],['S','-D','0','I','-D','D'],
           ['S','-D','I','0','D','-D'],['S','D','-D','D','0','-I'],['S','D','D','-D','-I','0']]
    a=[[x for name in names for x in sym[name][r]] for names in table for r in range(2)]
    return mm(a,tensor(eye(6),F))

def fills(w):
    n=len(w);m=n//2
    a={(i,j):[[x//2 for x in row] for row in mm(block(w,i,j),F)]
       for i,j in product(range(m),repeat=2) if i!=j}
    assert all(value in GROUP for value in a.values())
    answers=[]
    for root in GROUP:
        states=[root]+[neg(mm(mm(a[j,0],tr(root)),a[0,j])) for j in range(1,m)]
        if any(add(mm(a[i,j],tr(states[j])),mm(states[i],tr(a[j,i])))!=[[0,0],[0,0]]
               for i,j in combinations(range(m),2)):continue
        x=[[0]*n for _ in range(n)]
        for i,state in enumerate(states):
            small=mm(state,F)
            for r,c in product(range(2),repeat=2):x[2*i+r][2*i+c]=small[r][c]
        h=add(w,x)
        assert mm(h,tr(h))==eye(n,n)
        answers.append({'root':root,'hadamard':h})
    return answers

def reflect(w,selected,signs):
    n=len(w);r=len(selected);flipped=[]
    for j in range(n):
        values=[w[i][j] for i in selected]
        inner=dot(values,signs)
        if any(x==0 for x in values):
            if inner:return None
        elif inner not in (0,r,-r):return None
        if inner:flipped.append(j)
    changed=[row[:] for row in w]
    for i in selected:
        for j in flipped:changed[i][j]*=-1
    assert mm(changed,tr(changed))==eye(n,n-2)
    assert all((changed[i][j]==0)==(w[i][j]==0) for i,j in product(range(n),repeat=2))
    return changed,flipped

def normalize_zeros(w):
    sets=sorted({tuple(j for j,x in enumerate(row) if x==0) for row in w})
    rows=[i for zeros in sets for i,row in enumerate(w) if tuple(j for j,x in enumerate(row) if x==0)==zeros]
    columns=[j for zeros in sets for j in zeros]
    normal=[[w[i][j] for j in columns] for i in rows]
    assert len(rows)==len(columns)==len(w)
    return normal,rows,columns

def switch_four(w,blocks):
    selected=[i for b in blocks for i in (2*b,2*b+1)]
    h4=[[1-2*((i&j).bit_count()%2) for j in range(4)] for i in range(4)]
    raw=mm(h4,[w[i] for i in selected])
    assert all(x%2==0 for row in raw for x in row)
    changed=[row[:] for row in w]
    for i,row in zip(selected,raw):changed[i]=[x//2 for x in row]
    if any(x not in (-1,0,1) for row in changed for x in row):return None
    assert mm(changed,tr(changed))==eye(len(w),len(w)-2)
    normal,rows,columns=normalize_zeros(changed)
    answers=[]
    for item in fills(normal):
        h=[[0]*len(w) for _ in w]
        for r,i in enumerate(rows):
            for c,j in enumerate(columns):h[i][j]=item['hadamard'][r][c]
        assert mm(h,tr(h))==eye(len(w),len(w))
        old_violations=sum(w[i][j]!=0 and h[i][j]!=w[i][j] for i,j in product(range(len(w)),repeat=2))
        answers.append({'old_nonzero_violations':old_violations,'hadamard':h})
    return {'row_blocks':blocks,'affected_rows':selected,'switched_weighing':changed,
            'entry_changes':sum(w[i][j]!=changed[i][j] for i,j in product(range(len(w)),repeat=2)),
            'old_nonzeros_changed_or_erased':sum(w[i][j]!=0 and w[i][j]!=changed[i][j] for i,j in product(range(len(w)),repeat=2)),
            'zero_positions_changed':sum((w[i][j]==0)!=(changed[i][j]==0) for i,j in product(range(len(w)),repeat=2)),
            'normalizing_rows':rows,'normalizing_columns':columns,
            'completion_count':len(answers),'completions':answers}

if __name__=='__main__':
    w=original();assert mm(w,tr(w))==eye(12,10) and not fills(w)
    admissible=[];repairs=[];tried=0
    selections=[]
    for count in (3,4):
        selections.extend(tuple(i for b in blocks for i in (2*b,2*b+1)) for blocks in combinations(range(6),count))
    selections.extend(selection for selection in combinations(range(12),3) if len({i//2 for i in selection})==3)
    for selected in selections:
        for tail in product((-1,1),repeat=len(selected)-1):
            signs=(1,)+tail;tried+=1
            switched=reflect(w,selected,signs)
            if switched is None:continue
            changed,columns=switched
            if not columns:continue
            completions=fills(changed)
            item={'selected_rows':selected,'selector_signs':signs,'flipped_columns':columns,
                  'nonzero_entry_changes':len(selected)*len(columns),'sign_fill_count':len(completions)}
            admissible.append(item)
            if completions:
                repairs.append({**item,'switched_weighing_matrix':changed,'hadamard_completion':completions[0]})
    result={'status':'passed','selector_cases':tried,'nontrivial_admissible_switches':len(admissible),
            'admissible_profiles':admissible,'repairs':sorted(repairs,key=lambda a:a['nonzero_entry_changes'])}
    four_switches=[]
    for blocks in combinations(range(6),2):
        candidate=switch_four(w,blocks)
        if candidate is not None:four_switches.append(candidate)
    assert len(four_switches)==1 and tuple(four_switches[0]['row_blocks'])==(0,1)
    assert four_switches[0]['completion_count']==2
    result['four_row_switches']=four_switches
    result['original_unfillable']=True
    result['scope']='Explicit support-moving four-row repair; no claim of globally minimal entry changes.'
    (HERE/'checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'selector_cases':tried,'admissible_fixed_support_reflections':len(admissible),
                      'support_moving_four_row_repairs':len(four_switches),
                      'entry_changes':four_switches[0]['entry_changes'],
                      'old_nonzeros_changed_or_erased':four_switches[0]['old_nonzeros_changed_or_erased'],
                      'completion_old_nonzero_violations':[a['old_nonzero_violations'] for a in four_switches[0]['completions']]}))
