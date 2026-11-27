# SPDX-License-Identifier: Apache-2.0
"""Independent binary exhaustive orthogonality check of the stored witness."""
from pathlib import Path
import json,itertools,importlib.util
root=Path(__file__).resolve().parent
w=json.loads((root/'search.json').read_text())['trap']
rows=w['signs'];assert len(rows)==12
masks=[sum((x==-1)<<j for j,x in enumerate(row)) for row in rows]
assert all(row[0]==1 for row in rows)
assert all((a^b).bit_count()==(0 if i==j else 10)
           for i,a in enumerate(masks) for j,b in enumerate(masks))
existing=set(masks);counts={};best=-1;bestmask=None;groups={}
for tail in range(1<<19):
    mask=tail<<1
    if mask in existing:continue
    compatible=sum((mask^row).bit_count()==10 for row in masks)
    counts[compatible]=counts.get(compatible,0)+1
    if compatible>best:best,bestmask=compatible,mask
    if compatible==10:
        missing=tuple(i for i,row in enumerate(masks) if (mask^row).bit_count()!=10)
        groups.setdefault(missing,[]).append(mask)
assert counts.get(12,0)==0
result=dict(passed=True,normalizedSignsEnumerated=1<<19,
            newSignCompatibilityCounts=counts,maximumCompatibleRows=best,
            minimumOldRowsDeletedToAdmitNewSign=12-best,
            bestNewSign=[-1 if (bestmask>>j)&1 else 1 for j in range(20)])
(root/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
largest=0;witness=None
for missing,values in groups.items():
    for size in range(len(values),largest,-1):
        found=next((t for t in itertools.combinations(values,size)
                    if all((a^b).bit_count()==10 for a,b in itertools.combinations(t,2))),None)
        if found is not None:largest=size;witness=(missing,found);break
assert largest==10 and witness[0]==(3,8)
newrows=[[-1 if (m>>j)&1 else 1 for j in range(20)] for m in witness[1]]
kept=[row for i,row in enumerate(rows) if i not in witness[0]]
completed=kept+newrows
assert all(sum(a*b for a,b in zip(x,y))==20*(i==j)
           for i,x in enumerate(completed) for j,y in enumerate(completed))
spec=importlib.util.spec_from_file_location('codes',root.parent/'codes/check.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)
old=tuple(tuple(row) for row in w['basis']);new=cc.rref(completed,5)
assert len(cc.rref(kept,5))==9 and len(new)==10
assert len(cc.rref(list(old)+list(new),5))==11
assert cc.pivot_code(old,newrows[0],5)==new
assert len(cc.sign_words_from_systematic(new,5))==20
exchange=dict(deletedOldRowIndices=witness[0],newSignMasks=witness[1],newRows=newrows,
              resultingFrameSize=20,retainedRank=9,newCodeRank=10,unionRank=11,
              minimumOldRowLoss=2,oneNeighborPivot=True)
(root/'exchange.json').write_text(json.dumps(exchange,indent=2)+'\n')
print('Exact minimum-two-row-loss self-dual neighbor reaches a full Hadamard20.')
