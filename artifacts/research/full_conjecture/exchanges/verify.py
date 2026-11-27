"""Independent full-cube verification of the three-row deletion obstruction.

Unlike augment.py this code uses neither rational elimination nor free
coordinates. It exhausts all 2^23 sign vectors up to global negation,
collects their nonorthogonality supports, and checks every deletion set.
"""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent


def main():
    data=json.loads((HERE/'partial24.json').read_text(encoding='utf-8'))
    rows=data['deadEnds'][0];n=24
    assert len(rows)==16
    assert all((a^b).bit_count()==12 for a,b in combinations(rows,2))
    small=[]
    for x in range(0,1<<n,2):
        bad=0;k=0
        for i,r in enumerate(rows):
            if (x^r).bit_count()!=n//2:
                bad|=1<<i;k+=1
                if k>2:break
        else:small.append((x,bad))
    checks=[]
    for k in (0,1,2):
        for deleted in combinations(range(len(rows)),k):
            allow=sum(1<<i for i in deleted)
            candidates=[x for x,bad in small if bad&~allow==0]
            for chosen in combinations(candidates,k+1):
                assert not all((a^b).bit_count()==n//2 for a,b in combinations(chosen,2))
            checks.append({'deleted':deleted,'candidateCount':len(candidates)})
    cert=json.loads((HERE/'augmentation24.json').read_text(encoding='utf-8'))
    assert cert['minimalDeletedRows']==3
    kept=[x for i,x in enumerate(rows) if i not in cert['deleted']]
    assert sorted(kept+cert['newMasks'])==sorted(cert['augmentedMasks'])
    for witness,size in ((cert['augmentedMasks'],17),(cert['completedMasks'],24)):
        assert len(witness)==size
        assert all((a^b).bit_count()==12 for a,b in combinations(witness,2))
    out={'n':n,'rows':rows,'allNormalizedSignVectorsTested':1<<(n-1),
         'smallNonorthogonalitySupports':small,'deletionChecks':checks,
         'noAugmentationDeletingAtMost':2,'threeForFourExchangeChecked':True,
         'full24CompletionGramChecked':True,'passed':True}
    (HERE/'independent24.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    summary={'normalizedVectorsExhausted':1<<23,'deletionSetsChecked':len(checks),
             'smallSupportCandidateCounts':dict(Counter(b.bit_count() for x,b in small)),
             'pairDeletionCandidateCounts':dict(Counter(x['candidateCount'] for x in checks if len(x['deleted'])==2)),
             'minimalDeletedRows':3,'fullCompletionChecked':True,'passed':True}
    (HERE/'verification.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
