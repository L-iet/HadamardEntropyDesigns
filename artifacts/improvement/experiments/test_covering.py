import unittest
from covering import covering_profile, monoid_values
from entropy import count_golay_monoid, entropy_certificate
from math import comb


class CoveringTests(unittest.TestCase):
    def test_bitsets_against_independent_unbounded_coin_dp(self):
        for bases in [(2, 3), (2, 10), (2, 10, 26)]:
            limit = 3000
            values = monoid_values(bases, limit)
            costs = [0] + [limit + 1] * limit
            for total in range(1, limit + 1):
                costs[total] = min(1 + costs[total - v] for v in values if v <= total)
            profile = covering_profile(bases, limit, 5)
            for row in profile['rows']:
                expected = next((n for n in range(1, limit + 1) if costs[n] > row['maxTerms']), None)
                self.assertEqual(row['firstMissing'], expected)

    def test_known_small_double_base_values(self):
        profile = covering_profile((2, 3), 20000, 4)
        self.assertEqual([r['firstMissing'] for r in profile['rows']], [5, 23, 431, 18431])

    def test_integer_lattice_count_against_explicit_enumeration(self):
        for N in [1, 2, 10, 26, 100, 1000, 10000, 1000000]:
            self.assertEqual(count_golay_monoid(N), len(monoid_values((2,10,26),N)))

    def test_entropy_certificates(self):
        for m in [1, 3, 7, 10]:
            certificate = entropy_certificate(m)
            N, T = int(certificate['N']), certificate['allowedValuesThroughN']
            self.assertEqual(N, 2 ** certificate['upperExponentBase2'])
            self.assertEqual(T, count_golay_monoid(N))
            self.assertEqual(int(certificate['multisetCount']), comb(T+m,m))
            self.assertLess(comb(T+m,m), N)


if __name__ == '__main__':
    unittest.main()
