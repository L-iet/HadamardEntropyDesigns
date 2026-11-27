# SPDX-License-Identifier: Apache-2.0
"""Bounded exact-small-Gaussian search for codimension-two obstructions."""
from itertools import product,combinations
from pathlib import Path
import random,json
root=Path(__file__).resolve().parent
phases=(1,1j,-1,-1j)
def dot(a,b):return sum(x*complex(y).conjugate() for x,y in zip(a,b))
out=[]
for n,trials in ((6,100),(8,500)):
    candidates=[(1,)+tail for tail in product(phases,repeat=n-1) if 1+sum(tail)==0]
    rng=random.Random(20261120+n);complete=0;obstruction=None
    for trial in range(trials):
        rows=[(1,)*n];available=candidates[:]
        while len(rows)<n-2 and available:
            row=rng.choice(available);rows.append(row)
            available=[v for v in available if dot(v,row)==0]
        if len(rows)!=n-2:continue
        complete+=1
        columns=list(zip(*rows))
        k=[[n*(i==j)-dot(a,b) for j,b in enumerate(columns)] for i,a in enumerate(columns)]
        triple=next((t for t in combinations(range(n),3)
                     if all(abs(k[i][j])**2==2 for i,j in combinations(t,2))),None)
        if triple:
            obstruction=dict(trial=trial,rows=[[phases.index(z) for z in row] for row in rows],triple=triple);break
    out.append(dict(n=n,requestedTrials=trials,completedFrames=complete,obstruction=obstruction,candidateRows=len(candidates)))
(root/'search.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
