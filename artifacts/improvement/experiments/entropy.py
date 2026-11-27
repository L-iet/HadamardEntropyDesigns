"""Integer-only entropy certificates and numerical values of asymptotic constants.

Copyright (c) 2026 Joshua Mark. Released under Apache-2.0.
"""
from pathlib import Path
from math import comb, factorial, log, prod
import json


def count_golay_monoid(N):
    """Count distinct 2^a 10^b 26^c <= N without floating-point logs.
    Uniqueness follows by comparing prime valuations at 5, 13 and then 2.
    """
    count, c = 0, 1
    while c <= N:
        bc = c
        while bc <= N:
            count += (N // bc).bit_length()
            bc *= 10
        c *= 26
    return count


def entropy_certificate(m):
    def valid(k):
        N = 1 << k
        T = count_golay_monoid(N)
        return comb(T + m, m) < N
    low, high = 0, 1
    while not valid(high):
        low, high = high, 2 * high
    # Only claim validity of the returned upper endpoint, not minimality.
    while high - low > 1:
        middle = (low + high) // 2
        if valid(middle): high = middle
        else: low = middle
    N, T = 1 << high, count_golay_monoid(1 << high)
    count = comb(T + m, m)
    assert count < N
    return {'maxTerms': m, 'upperExponentBase2': high,
            'N': str(N), 'allowedValuesThroughN': T,
            'multisetCount': str(count), 'strictCountInequality': True}


def main():
    root = Path(__file__).resolve().parents[1]
    data = {'certificates': [entropy_certificate(m) for m in [1,2,3,4,5,6,7,10,20,50,100]],
            'secondOrderConstants': []}
    for bases in [(2,10),(2,10,26)]:
        r = len(bases)
        A = 1 / (factorial(r) * prod(log(b) for b in bases))
        beta = 1 + log(A) + r * log(r - 1)
        data['secondOrderConstants'].append({'bases':bases,'simplexCoefficient':A,'beta':beta,
                                            'status':'decimal illustration; proofs use exact logarithmic expressions'})
    (root/'data/entropy.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    for item in data['certificates']:
        print('m',item['maxTerms'],'ell <= 2^',item['upperExponentBase2'])
    print(data['secondOrderConstants'])


if __name__ == '__main__': main()
