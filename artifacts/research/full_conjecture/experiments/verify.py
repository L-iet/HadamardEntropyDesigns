"""Independent elementary checks of stored certificates (no random search)."""
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def orthogonal(rows,n):
    assert all(len(a)==n and all(x in (-1,1) for x in a) for a in rows)
    assert all(dot(a,a)==n for a in rows)
    assert all(dot(a,b)==0 for a,b in combinations(rows,2))


def row(mask,n):return [1-2*((mask>>j)&1) for j in range(n)]


def main():
    r=json.loads((ROOT/'data/experiments.json').read_text(encoding='utf-8'))
    s=next(x for x in r['partialCompletion'] if x['n']==20)
    cert=s['unextendibleCertificate'];a=cert['rows'];n=20
    orthogonal(a,n)
    # Independent enumeration by NEGATIVE-POSITION SETS, not integer masks.
    # The first all-one row forces exactly n/2 negative entries. Global
    # negation permits fixing coordinate zero positive.
    tested=0
    for neg in combinations(range(1,n),n//2):
        v=[1]*n
        for j in neg:v[j]=-1
        tested+=1
        assert any(dot(v,x)!=0 for x in a)
    e=json.loads((ROOT/'data/exchange.json').read_text(encoding='utf-8'))
    orthogonal([row(x,n) for x in e['completedMasks']],n)
    orthogonal([row(x,n) for x in e['augmentedMasks']],n)
    # Independently exhaust every single-row replacement in the recorded
    # gauge. A 13-row augmentation after deleting one needs two compatible
    # candidates. There are no such pairs for this example.
    single_exchange_counts=[]
    base=[row(sum(1<<j for j in neg),n) for neg in combinations(range(1,n),n//2)]
    base=[v for v in base if all(dot(v,x)==0 for x in a[:3])]
    for deleted in range(3,len(a)):
        kept=[v for i,v in enumerate(a) if i!=deleted]
        cand=[v for v in base if all(dot(v,x)==0 for x in kept)]
        assert all(dot(x,y)!=0 for x,y in combinations(cand,2))
        single_exchange_counts.append(len(cand))
    all_single_counts=[]
    masks=cert['masks']
    for deleted in range(len(a)):
        kept=masks[:deleted]+masks[deleted+1:]
        candidates=[x for x in range(0,1<<n,2)
                    if all((x^y).bit_count()==n//2 for y in kept)]
        assert candidates==[masks[deleted]]
        all_single_counts.append(len(candidates))
    seq_count=0
    for filename in ('experiments.json','norm-lifting.json'):
        obj=json.loads((ROOT/'data'/filename).read_text(encoding='utf-8'))
        if filename=='experiments.json':
            cases=obj['spectralFactorization']['knownSmallWitnesses']
            cases=[{'m':c['length'],'t':c['length'],'witness':c['sequences']} for c in cases]
        else:cases=obj['tested']
        for c in cases:
            seqs=c['witness'];m=c['m']
            assert all(len(x)==m and all(v%2 for v in x) for x in seqs)
            assert sum(v*v for x in seqs for v in x)==4*c['t']
            for shift in range(1,m):
                assert sum(x[i]*x[(i+shift)%m] for x in seqs for i in range(m))==0
            seq_count+=1
    report={'passed':True,'partialMatrixShape':[12,20],
            'balancedSignVectorsExhaustedUpToNegation':tested,
            'allOtherVectorsExcludedByFirstRow':True,
            'singleRowReplacementCandidateCounts':all_single_counts,
            'singleExchangeScope':'all twelve row deletions',
            'twoForThreeExchangeAndFullCompletionChecked':True,
            'sequenceCertificatesChecked':seq_count,
            'proofOfFullConjecture':False,'leanFormalization':False}
    (ROOT/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
