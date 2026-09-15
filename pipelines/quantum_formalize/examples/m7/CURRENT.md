# M7 formalization status

In progress; the original complete M7 Lean root remains pending. All 56 frozen natural-language source files were hash-checked; SOURCE.json records their identities.

**107 targets in 12 completed component batches** passed combined compilation, exact-target/source/payload/axiom checks and unchanged-environment checks.

| Batch | Accepted | Scope |
| --- | ---: | --- |
| [supports](supports/experiment/result.json) | 6 | Actual support polynomials |
| [selection](selection/experiment/result.json) | 12 | Pareto/lex winners, ties, emptiness and dominators |
| [factorized](factorized/experiment/result.json) | 6 | Independent-shift arithmetic numerator |
| [action](action/experiment/result.json) | 13 | Actual unit/exchange/two-shift laws and cardinality |
| [domain](domain/experiment/result.json) | 6 | Support-to-M6 domain interfaces |
| [orbit_fibers](orbit_fibers/experiment/result.json) | 7 | Full stabilizer fibers and exact division |
| [presentation](presentation/experiment/result.json) | 12 | Factored least-preimage algorithm and unique images |
| [prefix_sector](prefix_sector/experiment/result.json) | 9 | Actual M5 arithmetic sector counts and leaf rules |
| [group](group/experiment/result.json) | 6 | Actual group instances and stabilizer count specialization |
| [canonical_block](canonical_block/experiment/result.json) | 13 | Exact single-block normalization and translation equivalence |
| [cyclic_substitution](cyclic_substitution/experiment/result.json) | 8 | Full-modulus quotient root and unit-power identities |
| [actual_presentation](actual_presentation/experiment/result.json) | 9 | Actual four-field record order and unique winning presentations |

Active work:

- `canonical_outer`: actual unit/exchange canonical representative, realizing action and complete invariant (17 targets; preflight).
- `actual_factorized`: actual separated shift numerator and full-stabilizer quotient (8 targets; running).
- `prefix_completed`: literal completed supports and actual binary arithmetic child partitions (12 targets; running/repair).
- `signature_ideal`: full gcd via actual cyclic quotient ideals, preserving multiplicities (5 targets; running).
- `quotient_auto`: actual substitution composition, inverse and polynomial action (8 targets; preflight).
- `transport`: actual M6 logical, distance and minimum-witness action transport (7 targets; running).
- `default_query`: literal signatures, actual M6 distance, joint locality, two sector modes and explicit invalid-input rejection (8 targets; preflight).

Original remaining integration gates include the subgroup-connectedness/anchored-gcd equivalence, full signature and degree transport, actual compact residual generation and structural coverage, complete default-query/global-optimum integration, replay and original resource bounds. A component theorem does not establish the final root; no supplied complete transversal, count identity or distance oracle may remain there.

The frozen definitions and goals are preserved through repairs. Successful late live proofs are retained. Explicit local tactic repairs are independently checked and then pass normal exact-target replay; their origins and all failures are preserved. LeanExplore broader-query recovery records the actual fallback query and original unavailable requests; persistent failures remain unavailable.

Model gpt-6-astra / medium, two workers per active batch under the shared-host load, five live attempts per run and 600-second compiler calls, within the authorized 16-worker pipeline ceiling. Both Mathlib and Physlib are searched. The legacy `m5_formalized` scheduler field is not an M7 result. No complete-M7 acceptance record has been issued.
