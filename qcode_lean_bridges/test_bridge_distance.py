#!/usr/bin/env python3

import unittest

from bridge_distance import (
    label_bound,
    logical_bases,
    nullspace_basis,
    orthogonal,
    quotient_basis,
    verify_certificate,
)


class DistanceBridgeTests(unittest.TestCase):
    def test_label_bound(self):
        self.assertEqual(label_bound("[[144,24,<=12]]"), (144, 24, 12))
        self.assertEqual(label_bound("[[72,12,6]]"), (72, 12, 6))
        self.assertIsNone(label_bound("[[360,40]] (15,12)"))

    def test_nullspace_and_quotient(self):
        rows = [0b110]
        kernel = nullspace_basis(rows, 3)
        self.assertEqual(len(kernel), 2)
        self.assertTrue(all(orthogonal(rows, vector) for vector in kernel))
        quotient = quotient_basis(kernel, rows)
        self.assertEqual(len(quotient), 1)

    def test_css_logical_bases(self):
        hx = [0b110]
        hz = [0b110]
        lx, lz = logical_bases(hx, hz, 3)
        self.assertEqual((len(lx), len(lz)), (1, 1))

    def test_certificate_verification(self):
        # [110] is a self-orthogonal CSS check.  The vector 111 has zero
        # syndrome, odd self-pairing, and hence is a nontrivial logical.
        verify_certificate("X", 0b111, 0b111, 3, [0b110], [0b110], 3)
        with self.assertRaisesRegex(ValueError, "weight"):
            verify_certificate("X", 0b111, 0b111, 2, [0b110], [0b110], 3)
        with self.assertRaisesRegex(ValueError, "pair"):
            verify_certificate("X", 0b111, 0b000, 3, [0b110], [0b110], 3)


if __name__ == "__main__":
    unittest.main()
