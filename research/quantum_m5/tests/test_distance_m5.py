"""Check the SAT formulation against exhaustive physical operators at small N."""
import itertools
import unittest
from unittest.mock import patch

from scripts.distance_m5 import css, distance


class DistanceM5Tests(unittest.TestCase):
    def test_exhaustive_small_codes(self):
        count = 0
        for n in range(2, 6):
            supports = [(0, i) for i in range(1, n)] + [(0,)]
            for a, b in itertools.product(supports, repeat=2):
                hx, hz = css(n, a, b)
                # Enumerate the row space directly, without a logical quotient basis.
                stabilizers = {0}
                for row in hx:
                    stabilizers |= {v ^ row for v in list(stabilizers)}
                weights = [v.bit_count() for v in range(1, 1 << (2*n))
                           if v not in stabilizers and all((v & z).bit_count() % 2 == 0 for z in hz)]
                expected = min(weights) if weights else None
                result = distance(dict(N=n, A=list(a), B=list(b)), timeout=5)
                self.assertEqual(result['distance'], expected, (n, a, b, result))
                self.assertEqual(result['status'], 'exact' if weights else 'no_logical_qubits')
                count += 1
        self.assertEqual(count, 54)

    def test_reject_aliased_supports(self):
        with self.assertRaises(ValueError):
            css(4, [0, 4], [0, 1])
        with self.assertRaises(ValueError):
            css(4, [0, 0], [0, 1])

    def test_unknown_is_not_a_lower_bound(self):
        with patch('scripts.distance_m5.query', return_value=dict(status='unknown', witness=None)):
            result = distance(dict(N=6, A=[0, 3], B=[0, 1]))
        self.assertEqual(result['status'], 'bounds')
        self.assertEqual(result['d_lower'], 1)
        self.assertIsNone(result['distance'])


if __name__ == '__main__':
    unittest.main()
