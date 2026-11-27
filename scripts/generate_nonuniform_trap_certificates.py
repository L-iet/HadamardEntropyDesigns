# Copyright (c) 2026 Joshua Mark. SPDX-License-Identifier: Apache-2.0
# Original exact rational certificate generation; Python standard library only.
from fractions import Fraction as F
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
(ROOT/".lake").mkdir(parents=True,exist_ok=True)

def rank(rows):
    a=[list(map(F,r)) for r in rows]; k=0
    if not a:return 0
    for j in range(len(a[0])):
        pivot=next((i for i in range(k,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[k],a[pivot]=a[pivot],a[k]; v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k

def inverse(a):
    n=len(a);a=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        i=next(i for i in range(j,n) if a[i][j]);a[j],a[i]=a[i],a[j]
        v=a[j][j];a[j]=[x/v for x in a[j]]
        for i in range(n):
            if i!=j:
                v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return [r[n:] for r in a]

def lean(q):
    q=F(q)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'

prefix=r"""/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CollisionLocalMaxima
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace EntropyDesigns
abbrev SmallTrapMomentIndex (d : Nat) := Unit ⊕ (Fin d ⊕ (Fin d×Fin d))

def rationalTrapMomentMatrix (d : Nat) : Matrix (SmallTrapMomentIndex d) (Fin d → Bool) ℚ :=
  Sum.elim (fun _ _ => 1) (Sum.elim (fun i x => (bitSign (x i) : ℚ))
    (fun ij x => (bitSign (x ij.1) : ℚ)*(bitSign (x ij.2) : ℚ)))

def rationalTrapMomentTarget (d : Nat) : SmallTrapMomentIndex d → ℚ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0) (fun ij => if ij.1=ij.2 then 1 else 0))

"""
out=[prefix]; records=[]
for d,name in [(4,'four'),(5,'five')]:
    signs=[[F(-1 if x>>i&1 else 1) for x in range(1<<d)] for i in range(d)]
    a=[[F(1)]*(1<<d)]+signs+[[signs[i][x]*signs[j][x] for x in range(1<<d)] for i in range(d) for j in range(d)]
    p=[F(1,6) if x==0 else F(1,12) if x.bit_count() in ({2,3} if d==4 else {3}) else F(0) for x in range(1<<d)]
    supp=[x for x,v in enumerate(p) if v]; chosen=[]; rows=[]
    for r,row in enumerate(a):
        v=[row[x] for x in supp]
        if rank(rows+[v])>len(rows):chosen.append(r);rows.append(v)
        if len(rows)==len(supp):break
    inv=inverse(rows);left=[[F(0)]*len(a) for _ in p]
    for j,x in enumerate(supp):
        for k,r in enumerate(chosen):left[x][r]=inv[j][k]
    c=F(1,144 if d==4 else 216)
    y=[F(7,72)]+[c]*d+[c if i<j else F(0) for i in range(d) for j in range(d)]
    dual=[sum(y[r]*a[r][x] for r in range(len(a))) for x in range(1<<d)]
    assert len(supp)==11 and sum(p)==1 and sum(x*x for x in p)==F(7,72)
    assert all(sum(a[r][x]*p[x] for x in range(1<<d))==(F(1) if r==0 or r> d and (r-d-1)//d==(r-d-1)%d else F(0)) for r in range(len(a)))
    assert all(dual[x]==p[x] if p[x] else dual[x]>0 for x in range(1<<d))
    assert all(sum(left[x][r]*a[r][z] for r in range(len(a)))==F(x==z) for x in supp for z in supp)
    n=1<<d; m=len(a)
    out.append(f'def {name}TrapNegativeCount (x : Fin {d} → Bool) : Nat := (Finset.univ.filter (fun i => x i=true)).card\n')
    cond=f'{name}TrapNegativeCount x=2 ∨ {name}TrapNegativeCount x=3' if d==4 else f'{name}TrapNegativeCount x=3'
    out.append(f'def {name}TrapRationalWeights (x : Fin {d} → Bool) : ℚ := if {name}TrapNegativeCount x=0 then 1/6 else if {cond} then 1/12 else 0\n')
    out.append(f'theorem {name}TrapSeedNumber_bound : ∀ x : Fin {d} → Bool,(∑ i : Fin {d},if x i then 2^i.val else 0)<{n} := by decide +kernel\n')
    out.append(f'def {name}TrapSeedNumber (x : Fin {d} → Bool) : Fin {n} := ⟨∑ i : Fin {d},if x i then 2^i.val else 0,{name}TrapSeedNumber_bound x⟩\n')
    out.append(f'def {name}TrapMomentNumber : SmallTrapMomentIndex {d} → Fin {m} := Sum.elim (fun _ => 0) (Sum.elim (fun i => ⟨1+i.val,by omega⟩) (fun ij => ⟨{1+d}+ij.1.val*{d}+ij.2.val,by omega⟩))\n')
    table=';\n  '.join(','.join(lean(x) for x in r) for r in left)
    out.append(f'def {name}TrapInterpolationTable : Matrix (Fin {n}) (Fin {m}) ℚ := !![{table}]\n')
    out.append(f'def {name}TrapRationalInterpolation (x : Fin {d} → Bool) (r : SmallTrapMomentIndex {d}) : ℚ := {name}TrapInterpolationTable ({name}TrapSeedNumber x) ({name}TrapMomentNumber r)\n')
    out.append(f'def {name}TrapRationalDual : SmallTrapMomentIndex {d} → ℚ := Sum.elim (fun _ => 7/72) (Sum.elim (fun _ => {lean(c)}) (fun ij => if ij.1.val < ij.2.val then {lean(c)} else 0))\n')
    out.append(f'theorem {name}Trap_rational_feasibility : (∀ x,0≤{name}TrapRationalWeights x) ∧ (∑ x,{name}TrapRationalWeights x)=1 ∧ (∀ r,(∑ x,{name}TrapRationalWeights x*rationalTrapMomentMatrix {d} r x)=rationalTrapMomentTarget {d} r) ∧ (∑ x,({name}TrapRationalWeights x)^2)=7/72 := by decide +kernel\n')
    out.append(f'theorem {name}Trap_rational_interpolation : ∀ x t : Fin {d} → Bool,{name}TrapRationalWeights x≠0 → {name}TrapRationalWeights t≠0 → (∑ r : SmallTrapMomentIndex {d},{name}TrapRationalInterpolation x r*rationalTrapMomentMatrix {d} r t)=if t=x then 1 else 0 := by decide +kernel\n')
    out.append(f'theorem {name}Trap_rational_dual : ∀ x : Fin {d} → Bool,({name}TrapRationalWeights x≠0 → (∑ r : SmallTrapMomentIndex {d},{name}TrapRationalDual r*rationalTrapMomentMatrix {d} r x)={name}TrapRationalWeights x) ∧ ({name}TrapRationalWeights x=0 → 0<(∑ r : SmallTrapMomentIndex {d},{name}TrapRationalDual r*rationalTrapMomentMatrix {d} r x)) := by decide +kernel\n')
    records.append(dict(dimension=d,atoms=n,support=len(supp),independentMomentRows=chosen,maxDenominator=max(x.denominator for row in left for x in row)))
out.append('#print axioms fourTrap_rational_interpolation\n#print axioms fiveTrap_rational_interpolation\nend EntropyDesigns\n')
(ROOT/'.lake/NonuniformCertificateData.lean').write_text('\n'.join(out),encoding='utf-8',newline='\n')
(ROOT/'.lake/nonuniform-certificates.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print(json.dumps(records))
