import unittest
from .accepted_order import order_only_equivalent


class AcceptedOrderTests(unittest.TestCase):
    def setUp(self):
        self.a = 'import Mathlib\n\ntheorem Demo.a : True := by\n  trivial\n'
        self.b = 'theorem Demo.b : True := by\n  exact Demo.a\n'

    def test_permutation_is_diagnostic_not_compilation(self):
        left = self.a + self.b + '#print axioms Demo.a\n'
        right = 'import Mathlib\n' + self.b + self.a.split('\n', 1)[1]
        self.assertTrue(order_only_equivalent(left, right))

    def test_changed_proof_or_statement_is_rejected(self):
        for changed in [self.a.replace('trivial', 'exact True.intro'),
                        self.a.replace(': True', ': False')]:
            self.assertFalse(order_only_equivalent(self.a, changed))

    def test_other_commands_and_import_changes_are_rejected(self):
        for suffix in ['axiom bad : False\n', 'set_option autoImplicit false\n',
                       '#print axioms Foreign.theorem\n']:
            self.assertFalse(order_only_equivalent(self.a, self.a + suffix))
        self.assertFalse(order_only_equivalent(self.a, self.a.replace('Mathlib', 'Other')))

    def test_missing_or_duplicate_declarations_are_rejected(self):
        self.assertFalse(order_only_equivalent(self.a + self.b, self.a))
        self.assertFalse(order_only_equivalent(self.a + self.b, self.a + self.b + self.b))


if __name__ == '__main__':
    unittest.main()
