"""Test bounded row-exchange augmentation of an exact terminal obstruction."""
from itertools import combinations
from pathlib import Path
import json
from investigate import mask_row, gram, eye

ROOT = Path(__file__).resolve().parents[1]


def clique(pool, target, n):
    if target == 0:
        return []
    while len(pool) >= target:
        a, *tail = pool
        possible = [b for b in tail if (a ^ b).bit_count() == n//2]
        result = clique(possible, target-1, n)
        if result is not None:
            return [a]+result
        pool = tail
    return None


def repair(cert, n):
    rows = cert['masks']
    # Exhaust ALL single-row replacements, including deletion of the
    # all-one row (when balance cannot be assumed).
    all_single_counts=[]
    single_frozen=True
    for i in range(len(rows)):
        kept=rows[:i]+rows[i+1:]
        candidates=[x for x in range(0,1<<n,2)
                    if all((x^y).bit_count()==n//2 for y in kept)]
        all_single_counts.append(len(candidates))
        single_frozen &= candidates==[rows[i]]
    pool = [sum(1 << j for j in comb) for comb in combinations(range(1,n),n//2)]
    pool = [x for x in pool if all((x ^ y).bit_count() == n//2 for y in rows[:3])]
    attempts = []
    for remove_count in (1,2,3):
        for remove in combinations(range(3,len(rows)),remove_count):
            kept = [x for i,x in enumerate(rows) if i not in remove]
            candidates = [x for x in pool if all((x ^ y).bit_count() == n//2 for y in kept)]
            found = clique(candidates, remove_count+1,n)
            attempts.append({'removedIndices':remove,'candidateCount':len(candidates),
                             'augmentingCliqueExists':found is not None})
            if found is not None:
                augmented = kept+found
                assert gram([mask_row(x,n) for x in augmented]) == eye(len(augmented),n)
                # Complete this particular augmented witness by exact search,
                # rather than assuming the near-completion theorem.
                left = [x for x in pool if all((x ^ y).bit_count() == n//2 for y in augmented)]
                rest = clique(left,n-len(augmented),n)
                assert rest is not None
                completed = augmented+rest
                assert gram([mask_row(x,n) for x in completed]) == eye(n,n)
                return {'n':n,'originalRows':len(rows),'firstThreeRowsHeldFixed':True,
                        'allSingleRowReplacementsExhausted':True,
                        'allSingleRowReplacementCounts':all_single_counts,
                        'minimalDeletedRowsGlobally':2 if single_frozen and remove_count==2 else None,
                        'checkedRemovalCounts':list(range(1,remove_count+1)),
                        'minimalDeletedRowsWithFirstThreeFixed':remove_count,
                        'attempts':attempts,'removedIndices':remove,
                        'newMasks':found,'augmentedMasks':augmented,
                        'completedMasks':completed,
                        'claim':'one witness repaired; no universal augmentation theorem'}
    return {'n':n,'attempts':attempts,'found':False}


if __name__ == '__main__':
    r=json.loads((ROOT/'data/experiments.json').read_text(encoding='utf-8'))
    source=next(x for x in r['partialCompletion'] if x['n']==20)
    result=repair(source['unextendibleCertificate'],20)
    (ROOT/'data/exchange.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print({k:v for k,v in result.items() if k not in ('attempts','completedMasks','augmentedMasks')})
