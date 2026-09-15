# M7 formalization status

In progress; the original complete M7 Lean root remains pending. All 56 frozen natural-language source files were hash-checked; SOURCE.json records their identities.

**148 targets in 17 completed component batches** passed combined compilation, exact-target/source/payload/axiom checks and unchanged-environment checks.
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
| [signature_ideal](signature_ideal/experiment/result.json) | 5 | Full multiplicity-preserving gcd ideals and monic uniqueness |
| [quotient_auto](quotient_auto/experiment/result.json) | 8 | Concrete unit substitution composition, inverses and polynomial action |
| [prefix_completed](prefix_completed/experiment/result.json) | 12 | Actual support completions and arithmetic binary child partitions |
| [actual_factorized](actual_factorized/experiment/result.json) | 8 | Actual separated numerator and computed full-stabilizer quotient |
| [default_query](default_query/experiment/result.json) | 8 | Actual labels, distance, locality, sector modes and explicit invalid-input rejection |

Active work:

- `canonical_outer`: actual unit/exchange canonical representative, realizing action and complete invariant (17 targets; running, one local syntax repair under exact verification).
- `transport`: actual M6 logical, distance and minimum-witness action transport (7 targets; running).

- `affine_polynomial`: literal support-polynomial images under the actual affine action (7 targets; running).

- `quotient_degree`: cardinality of the full polynomial quotient and induced degree invariance (5 targets; preflight).

- `global_query`: optimum and all ties across the complete supplied class/action family (9 targets; running; generation completeness remains downstream).

Original remaining integration gates include the subgroup-connectedness/anchored-gcd equivalence, full signature and degree transport, actual compact residual generation and structural coverage, complete default-query/global-optimum integration, replay and original resource bounds. A component theorem does not establish the final root; no supplied complete transversal, count identity or distance oracle may remain there.

The frozen definitions and goals are preserved through repairs. Successful late live proofs are retained. Explicit local tactic repairs are independently checked and then pass normal exact-target replay; their origins and all failures are preserved. LeanExplore broader-query recovery records the actual fallback query and original unavailable requests; persistent failures remain unavailable.

Model gpt-6-astra / medium, two workers per active batch under the shared-host load, five live attempts per run and 600-second compiler calls, within the authorized 16-worker pipeline ceiling. Both Mathlib and Physlib are searched. The legacy `m5_formalized` scheduler field is not an M7 result. No complete-M7 acceptance record has been issued.
