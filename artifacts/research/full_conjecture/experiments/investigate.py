"""Exact, dependency-free tests of candidate bridges to Hadamard existence.

All arithmetic in certificates is integral. Searches are bounded experiments,
not asymptotic evidence. No third-party research code is used.
"""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parents[1]


def transpose(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def eye(n, scale=1):
    return [[scale*int(i == j) for j in range(n)] for i in range(n)]


def mask_row(mask, n):
    return [1-2*((mask >> j) & 1) for j in range(n)]


def gram(a):
    return mm(a, transpose(a))


def residual(a):
    n = len(a[0])
    g = gram(transpose(a))
    return [[n*int(i == j)-g[i][j] for j in range(n)] for i in range(n)]


def extensions(rows):
    """Exhaust ALL sign vectors up to global negation; first entry is +1."""
    n = len(rows[0])
    return [mask_row(mask, n) for mask in range(0, 1 << n, 2)
            if all(sum(x*y for x, y in zip(row, mask_row(mask, n))) == 0
                   for row in rows)]


def search_partial(n=16, trials=500, seed=20261120):
    rng = random.Random(seed)
    balanced = [sum(1 << j for j in comb)
                for comb in combinations(range(1, n), n//2)]
    fixed = [0, sum(1 << j for j in range(n//2, n)),
             sum(1 << j for j in range(n) if (j//(n//4)) % 2)]
    pool = [x for x in balanced if all((x ^ y).bit_count() == n//2 for y in fixed)]
    histogram = Counter()
    first = None
    for trial in range(trials):
        rows = fixed[:]
        choices = pool[:]
        while choices:
            row = rng.choice(choices)
            rows.append(row)
            choices = [x for x in choices if (x ^ row).bit_count() == n//2]
        histogram[len(rows)] += 1
        if len(rows) < n and first is None:
            first = {'trial': trial, 'masks': rows}
    out = {'n': n, 'trials': trials, 'seed': seed,
           'maximalRowCountHistogram': dict(sorted(histogram.items()))}
    if first:
        rows = [mask_row(x, n) for x in first['masks']]
        assert gram(rows) == eye(len(rows), n)
        assert not extensions(rows)
        c = residual(rows)
        assert mm(c, c) == [[n*x for x in row] for row in c]
        assert all(c[i][i] == n-len(rows) for i in range(n))
        out['unextendibleCertificate'] = {**first, 'rows': rows,
            'rankDefect': n-len(rows), 'residualGram': c,
            'allNormalizedSignVectorsTested': 1 << (n-1),
            'extensionCountUpToNegation': 0}
    return out


def optimization_trap(n):
    # V=nU=2J-nI; S=sign(U)=J-2I.  SU=2I+(1-4/n)J>0.
    v = [[2-n*int(i == j) for j in range(n)] for i in range(n)]
    s = [[1-2*int(i == j) for j in range(n)] for i in range(n)]
    assert gram(v) == eye(n, n*n)
    assert mm(s, v) == [[2*n*int(i == j)+n-4 for j in range(n)] for i in range(n)]
    assert n*(n-2) > 0 and 2*n > 0
    norm_numerator = sum(abs(x) for row in v for x in row)
    assert norm_numerator == n*(3*n-4)
    assert (3*n-4)**2 < n**3
    return {'n': n, 'orthogonalMatrixNumerator': v, 'denominator': n,
            'l1Norm': 3*n-4, 'l1NormSquared': (3*n-4)**2,
            'hadamardOptimumSquared': n**3,
            'scaledPolarEigenvalues': [n*(n-2), 2*n],
            'strictLocalMaximum': True, 'isHadamard': False}


def pac(seq):
    n = len(seq)
    return tuple(sum(seq[j]*seq[(j+s) % n] for j in range(n)) for s in range(n))


def four_complementary(n, fixed_sums=None):
    """Meet in the middle over pair autocorrelation sums, no symmetry assumed."""
    seqs = [(1,)+tail for tail in product((-1, 1), repeat=n-1)]
    if fixed_sums is None:
        buckets = [seqs]*4
    else:
        buckets = [[a for a in seqs if sum(a) == s] for s in fixed_sums]
    def key(a, b):
        return tuple(x+y for x, y in zip(pac(a)[1:], pac(b)[1:]))
    pairs = {}
    for a in buckets[0]:
        for b in buckets[1]:
            pairs.setdefault(key(a, b), (a, b))
    for c in buckets[2]:
        for d in buckets[3]:
            target = tuple(-x for x in key(c, d))
            if target in pairs:
                a, b = pairs[target]
                assert tuple(sum(v) for v in zip(*(pac(x) for x in (a,b,c,d)))) == (4*n,)+(0,)*(n-1)
                return (a,b,c,d)
    return None


def qmul(a, b):
    w,x,y,z = a
    W,X,Y,Z = b
    return (w*W-x*X-y*Y-z*Z, w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X, w*Z+x*Y-y*X+z*W)


def quaternion_autocorrelation(sequences):
    q = list(zip(*sequences))  # actual quaternion coefficients q_j/2
    n = len(q)
    return [tuple(sum(v) for v in zip(*(qmul(q[j],
                (q[(j+s)%n][0],)+tuple(-x for x in q[(j+s)%n][1:]))
                for j in range(n)))) for s in range(n)]  # divide by 4


def goethals_seidel(sequences):
    n = len(sequences[0])
    mats = [[[seq[(j-i) % n] for j in range(n)] for i in range(n)]
            for seq in sequences]
    a,b,c,d = mats
    rev = [[int((i+j) % n == 0) for j in range(n)] for i in range(n)]
    def neg(x): return [[-v for v in row] for row in x]
    br,cr,dr = (mm(x,rev) for x in (b,c,d))
    btr,ctr,dtr = (mm(transpose(x),rev) for x in (b,c,d))
    blocks = [[a,br,cr,dr], [neg(br),a,dtr,neg(ctr)],
              [neg(cr),neg(dtr),a,btr], [neg(dr),ctr,neg(btr),a]]
    h = [sum([blocks[bi][bj][i] for bj in range(4)], [])
         for bi in range(4) for i in range(n)]
    assert gram(h) == eye(4*n,4*n)
    return h


def spectral_tests():
    witnesses = []
    for n in (3,5,7,9):
        seqs = four_complementary(n)
        assert seqs
        h = goethals_seidel(seqs)
        witnesses.append({'length': n, 'sequences': seqs,
                          'rowSums': list(map(sum,seqs)),
                          'periodicAutocorrelations': list(map(pac,seqs)),
                          'quaternionAutocorrelationsNumerator': quaternion_autocorrelation(seqs),
                          'quaternionAutocorrelationsDenominator': 4,
                          'hadamardOrder': len(h)})
    # All + signs have the required row sums (3,3,1,1) at n=5 after
    # replacing the first two rows by weight-one negatives, but this
    # individual choice need not be complementary.
    bad = ((1,1,1,1,-1),)*2 + ((1,1,1,-1,-1),)*2
    assert sum(sum(a)**2 for a in bad) == 20
    assert any(sum(v) for v in list(zip(*(pac(a) for a in bad)))[1:])
    # Scalar four-square solutions can fail even to lift to binary
    # periodic complementary sequences. Check every ordered nonnegative
    # row-sum type at n=9; signed/permuted versions are equivalent.
    lifts = []
    n = 9
    from itertools import combinations_with_replacement
    for sums in combinations_with_replacement(range(1,n+1,2),4):
        if sum(s*s for s in sums) == 4*n:
            found = four_complementary(n,sums)
            lifts.append({'length': n, 'rowSums': sums, 'liftExists': found is not None,
                          'witness': found})
    return {'knownSmallWitnesses': witnesses,
            'zeroFrequencyOnlyCounterexample': {'length':5,'sequences':bad,
                'rowSums':list(map(sum,bad)),
                'summedPeriodicAutocorrelations':list(map(sum,zip(*(pac(a) for a in bad))))},
            'allNonnegativeRowSumTypesAtLength9': lifts}


def main():
    results = {'status': 'research experiments; no proof of all-order existence',
               'partialCompletion': [search_partial(), search_partial(n=20,trials=200)],
               'optimizationTraps': [optimization_trap(n) for n in (8,12,16)],
               'spectralFactorization': spectral_tests()}
    (ROOT/'data/experiments.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
    for r in results['partialCompletion']:
        print('Partial completion histogram:',r['n'],r['maximalRowCountHistogram'])
        print('Unextendible certificate:', 'unextendibleCertificate' in r)
    print('Exact local-maximum certificates:', len(results['optimizationTraps']))
    print('Four-sequence witnesses:',len(results['spectralFactorization']['knownSmallWitnesses']))
    print('Length-9 row-sum lifts:',results['spectralFactorization']['allNonnegativeRowSumTypesAtLength9'])


if __name__ == '__main__':
    main()
