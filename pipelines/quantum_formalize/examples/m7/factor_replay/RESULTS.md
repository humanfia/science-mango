# Full multiplicity factor replay

All four frozen targets passed normal harness exact-target/axiom acceptance, combined assembly and unchanged-environment gates. The finite coefficient pool is complete, the finite remainder-based irreducibility check is exact, and factor checking verifies distinct monic irreducibles with positive multiplicities and exact product. For every monic polynomial, the expected normalized-factor list with multiset counts passes the actual check, including the unit polynomial. No runtime extraction claim is made.

Run: `/home/jing/m7-lean-factor-replay-formalization/.humanize-formal-runs/explicit-replay-e6rjym9w/experiment`. Accepted attempts: {'pool_complete': 1, 'irreducible_check_exact': 1, 'factor_check_exact': 1, 'self_check': 2}. All drafts and receipts are preserved in experiment/.

The original pool proof succeeded on live attempt 2 and was replayed unchanged. Irreducibility required an independently checked explicit logical repair after five preserved failed drafts; this repair passed normal frozen replay. Factor-check exactness passed live attempt 1 and expected-factor self-check passed live attempt 2. All initial failures and independent repair checks are archived under experiments/.
