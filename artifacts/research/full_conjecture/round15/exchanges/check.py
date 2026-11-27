"""Exact original stdlib certificates for Hadamard-layer escape and row repair."""
from itertools import combinations
from pathlib import Path
import json

A=[84,44,30,230,133,73,111,51]
def energy(words,n):return 2*sum((n-2*(x^y).bit_count())**2 for x,y in combinations(words,2))
def signs(words,n):return [[1-2*((x>>j)&1) for j in range(n)] for x in words]
def walsh(m):return [[1-2*((p&q).bit_count()%2) for q in range(m)] for p in range(m)]
def layers(rows,B):
 m=len(B);N=len(rows[0]);n=N*m;answer=[]
 # Each rows[p] is an N-entry list of base-row negative masks.
 for i in range(N):
  for p in range(m):
   word=0
   for j in range(N):
    a=1-2*((rows[p][i]>>j)&1)
    for q in range(m):word|=int(a*B[p][q]<0)<<(j*m+q)
   answer.append(word)
 return answer

def entry_distance(x,y):return sum((a^b).bit_count() for a,b in zip(x,y))
assert energy(A,8)==152
single=[];pairmin=10**9
for c in range(64):
 a=A[:];a[c//8]^=1<<(c%8);single.append(energy(a,8)-152)
assert min(single)==8
for c,d in combinations(range(64),2):
 a=A[:]
 for x in [c,d]:a[x//8]^=1<<(x%8)
 pairmin=min(pairmin,energy(a,8)-152)
assert pairmin==0
basepath=[A[:]];a=A[:]
for c in [20,18,19]:a=a[:];a[c//8]^=1<<(c%8);basepath.append(a)
assert [energy(a,8) for a in basepath]==[152,160,152,128]
updates=[(3,2),(2,31),(6,103),(7,49)];stages=[A[:]];a=A[:]
for i,new in updates:a=a[:];a[i]=new;stages.append(a)
baseenergies=[energy(a,8) for a in stages]
assert baseenergies==[152,120,96,56,0]
assert sum((x^y).bit_count() for x,y in zip(stages[0],stages[-1]))==7
assert stages[-1]==[84,44,31,2,133,73,103,49]
cases=[]
for m in [2,4,8]:
 B=walsh(m);n=8*m;start=layers([A[:]]*m,B);assert energy(start,n)==152*m**3
 # Heterogeneous layers test the exact formula, not just tensor scaling.
 hetero=[stages[p%len(stages)] for p in range(m)]
 assert energy(layers(hetero,B),n)==m*m*sum(energy(a,8) for a in hetero)
 stripenergies=[];last=None
 for a in basepath:
  ap=[A[:]]*m;ap[0]=a;w=layers(ap,B);stripenergies.append(energy(w,n));last=w
 assert stripenergies==[152*m**3,152*m**3+8*m*m,152*m**3,152*m**3-24*m*m]
 assert entry_distance(start,last)==3*m and sum(x!=y for x,y in zip(start,last))==1
 # Four simultaneous block-row replacements.
 blockenergies=[energy(layers([a]*m,B),n) for a in stages]
 assert blockenergies==[e*m**3 for e in baseenergies]
 final=layers([stages[-1]]*m,B);assert energy(final,n)==0 and entry_distance(start,final)==7*m*m
 # Resolve each block-row update into m strictly improving ordinary-row moves.
 ap=[A[: ] for p in range(m)];ordinary=[energy(layers(ap,B),n)]
 for stage,(i,new) in enumerate(updates):
  for p in range(m):
   before=layers(ap,B);ap[p]=ap[p][:];ap[p][i]=new;after=layers(ap,B)
   assert sum(x!=y for x,y in zip(before,after))==1
   e=energy(after,n);assert e<ordinary[-1];ordinary.append(e)
   assert e-ordinary[-2]==(baseenergies[stage+1]-baseenergies[stage])*m*m
 assert ordinary[-1]==0 and len(ordinary)-1==4*m
 cases.append(dict(hadamardFactor=m,order=n,exactHeterogeneousLayerIdentity=True,stripEscapeEnergies=stripenergies,stripEscapeEntryChanges=3*m,stripEscapeRowsChanged=1,optimalStripBarrier=8*m*m,blockRowRepairEnergies=blockenergies,ordinaryRowRepairSteps=4*m,entryRepairCount=7*m*m,finalGramDefect=0))
out={'passed':True,'baseRows':A,'baseMinimumSingleCost':8,'baseMinimumPairCost':0,'baseStripPath':[152,160,152,128],'baseRowRepairStates':stages,'baseRowRepairEnergies':baseenergies,'cases':cases,'noGlobalMinimumEntryRepairClaim':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
