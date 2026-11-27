"""Exhaust bounded row deletions using exact low-dimensional cube search."""
from itertools import combinations
from pathlib import Path
import json
from cube_kernel import cube_kernel,row,clique

HERE=Path(__file__).resolve().parent


def augment(rows,n,bound=3):
    attempts=[]
    original=[row(x,n) for x in rows]
    for deleted_count in range(bound+1):
        count=0
        for deleted in combinations(range(len(rows)),deleted_count):
            kept=[v for i,v in enumerate(original) if i not in deleted]
            cand,cert=cube_kernel(kept,n)
            new=clique(cand,deleted_count+1,n)
            attempts.append({'deleted':deleted,'candidateCount':len(cand),'assignmentCount':cert['assignmentsTested'],
                             'augmentationExists':new is not None})
            count+=1
            if new is not None:
                masks=[v for i,v in enumerate(rows) if i not in deleted]+new
                assert len(masks)==len(rows)+1
                assert all((a^b).bit_count()==n//2 for a,b in combinations(masks,2))
                completion_pool,_=cube_kernel([row(x,n) for x in masks],n)
                finish=clique(completion_pool,n-len(masks),n)
                completed=None if finish is None else masks+finish
                if completed is not None:
                    assert len(completed)==n
                    assert all((a^b).bit_count()==n//2 for a,b in combinations(completed,2))
                return {'n':n,'oldRows':len(rows),'minimalDeletedRows':deleted_count,
                        'allSmallerDeletionSetsExhausted':True,'deleted':deleted,
                        'newMasks':new,'augmentedMasks':masks,'completedMasks':completed,
                        'attempts':attempts}
        print('Exhausted deletions:',deleted_count,count,flush=True)
    return {'n':n,'oldRows':len(rows),'noAugmentationDeletingAtMost':bound,
            'attempts':attempts}


if __name__=='__main__':
    d=json.loads((HERE/'partial24.json').read_text())
    rows=d['deadEnds'][0]
    result=augment(rows,24)
    (HERE/'augmentation24.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print({k:v for k,v in result.items() if k!='attempts'})
