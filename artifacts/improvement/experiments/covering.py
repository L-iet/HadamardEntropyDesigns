"""Exact finite covering experiments using only Python's standard library.

Copyright (c) 2026 Joshua Mark. Released under Apache-2.0.
No code is taken from the mathematical references.
"""
from pathlib import Path
import argparse
import json
import time


def monoid_values(bases, limit):
    values = {1}
    for base in bases:
        enlarged = set()
        for value in values:
            while value <= limit:
                enlarged.add(value)
                value *= base
        values = enlarged
    return sorted(values)


def covering_profile(bases, limit, max_terms):
    """Exact distinct-subset DP; for a monoid containing 2 this also
    answers the at-most-m problem with repetitions, by carrying equal terms.
    Every summand of a sum at most limit is itself at most limit.
    """
    start = time.perf_counter()
    values = monoid_values(bases, limit)
    mask = (1 << (limit + 1)) - 1
    layers = [1] + [0] * max_terms
    for index, value in enumerate(values):
        # Descending updates use each allowed value at most once.
        for weight in range(min(max_terms, index + 1), 0, -1):
            layers[weight] |= (layers[weight - 1] << value) & mask
    reachable, rows = 1, []
    for weight in range(1, max_terms + 1):
        reachable |= layers[weight]
        missing_bits = (~reachable) & mask & ~1
        first = (missing_bits & -missing_bits).bit_length() - 1 if missing_bits else None
        # Every integer below this power-of-two radix is certified covered.
        covered_end = first - 1 if first is not None else limit
        radix_bits = (covered_end + 1).bit_length() - 1
        rows.append({
            'maxTerms': weight,
            'firstMissing': first,
            'firstMissingStatus': 'exact' if first is not None else 'larger-than-cutoff',
            'coveredThrough': covered_end,
            'binaryRadixBits': radix_bits,
            'radix': 2 ** radix_bits,
            'exponentSlopeNumerator': 2 * weight,
            'exponentSlopeDenominator': radix_bits,
            'exponentSlope': 2 * weight / radix_bits if radix_bits else None,
        })
    return {'bases': list(bases), 'cutoff': limit, 'allowedValues': len(values),
            'algorithm': 'exact distinct-subset bitset dynamic programming',
            'rows': rows, 'seconds': round(time.perf_counter() - start, 3)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=2 ** 22)
    parser.add_argument('--terms', type=int, default=7)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data' / 'covering.json')
    args = parser.parse_args()
    reports = [covering_profile(b, args.limit, args.terms)
               for b in [(2, 3), (2, 10), (2, 10, 26)]]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(reports, indent=2) + '\n', encoding='utf-8')
    for report in reports:
        print('Bases', report['bases'], 'seconds', report['seconds'])
        for row in report['rows']:
            print(row['maxTerms'], row['firstMissing'], row['exponentSlope'])


if __name__ == '__main__':
    main()
