# M7 formalization status

In progress; the original complete M7 Lean root remains pending. All 56 frozen natural-language source files were hash-checked; SOURCE.json records their identities.

**348 targets in 43 completed component batches** passed combined compilation, exact-target/source/payload/axiom checks and unchanged-environment checks.

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
| [affine_polynomial](affine_polynomial/experiment/result.json) | 7 | Literal affine support images and invertible shift factors |
| [quotient_degree](quotient_degree/experiment/result.json) | 5 | Full quotient cardinality and induced degree invariance |
| [global_query](global_query/experiment/result.json) | 9 | Global family optima, all ties, winning dominators and unique physical output |
| [transport](transport/experiment/result.json) | 7 | Actual M6 distance and minimum-witness action transport |
| [signature_tau](signature_tau/experiment/result.json) | 10 | Actual M7 full-multiplicity signature substitution and reduced-source tau |
| [canonical_outer](canonical_outer/experiment/result.json) | 17 | M7 actual unit/exchange canonical representatives using separate block normalization |
| [residue_prefix](residue_prefix/experiment/result.json) | 10 | M7 arithmetic prefix counts on literal residue supports |
| [query_rebase](query_rebase/experiment/result.json) | 8 | M7 actual base-action reparameterization of global queries |
| [actual_signature](actual_signature/experiment/result.json) | 9 | Actual M7 literal recipe signature and source sector numerator |
| [canonical_classes](canonical_classes/experiment/result.json) | 6 | M7 actual canonical values discharge orbit separation and fresh insertion |
| [descent_trace](descent_trace/experiment/result.json) | 8 | M7 concrete finite descent-trace checker and original call bound |
| [orbit_residual](orbit_residual/experiment/result.json) | 12 | M7 actual disjoint-orbit residual invariant and strict insertion descent |
| [prefix_bits](prefix_bits/experiment/result.json) | 9 | M7 concrete binary prefix states and actual arithmetic descent partitions |
| [query_certificate](query_certificate/experiment/result.json) | 8 | M7 actual finite query certificate checker |
| [connectivity](connectivity/experiment/result.json) | 14 | M7 original within-block generated subgroup connectivity bridge |
| [recovery_prefix](recovery_prefix/experiment/result.json) | 3 | M7 actual residue-prefix geometry for arithmetic recovery |
| [closed_solve](closed_solve/experiment/result.json) | 1 | Original M7 connected anchored literal recipe receives the sealed actual M6 algorithm contract |
| [prefix_orbit](prefix_orbit/experiment/result.json) | 9 | M7 actual arithmetic orbit-prefix and residual invariant integration |
| [compact_core](compact_core/experiment/result.json) | 8 | M7 concrete compact emission records and finite recurrence structure |
| [arithmetic_loops](arithmetic_loops/experiment/result.json) | 5 | M7 actual arithmetic prefix character-loop cardinality bounds |
| [quality_table](quality_table/experiment/result.json) | 3 | Actual M6 class cache and concrete single-block quality arrays |
| [query_sectors](query_sectors/experiment/result.json) | 5 | M7 concrete complete query signature sectors |
| [recovery_instance](recovery_instance/experiment/result.json) | 7 | M7 actual arithmetic residual recovery instance |
| [raw_coverage](raw_coverage/experiment/result.json) | 6 | Original M7 raw structural orbit coverage from actual root exhaustion |
| [streaming_indices](streaming_indices/experiment/result.json) | 6 | M7 actual streaming action-index cursors and exact winners |
| [generation_calls](generation_calls/experiment/result.json) | 8 | M7 actual compact generator projection and original call bounds |

Active work:

- `compact_correctness`: thirteen exact actual-generator invariants running after parent acceptance.
- `generated_family` and `final_selector`: dependency-gated integration of the actual generated classes with raw global optima and unique presentations.
- `scalar_work` and `compact_storage`: original arithmetic and concrete bit-representation bounds, with preprocessing/bookkeeping/path exceptions explicit.
- `generation_replay`: concrete sequential certificate replay in preparation.

Original remaining integration gates include actual compact residual generation and structural coverage, complete default-query/global-optimum integration, replay and original resource bounds. Full signature transport and the component degree invariance are already accepted. A component theorem does not establish the final root; no supplied complete transversal, count identity or distance oracle may remain there.

The frozen definitions and goals are preserved through repairs. Successful late live proofs are retained. Explicit local tactic repairs are independently checked and then pass normal exact-target replay; their origins and all failures are preserved. LeanExplore broader-query recovery records the actual fallback query and original unavailable requests; persistent failures remain unavailable.

Model gpt-6-astra / medium, two workers per active batch under the shared-host load, five live attempts per run and 600-second compiler calls, within the authorized 16-worker pipeline ceiling. Both Mathlib and Physlib are searched. The legacy `m5_formalized` scheduler field is not an M7 result. No complete-M7 acceptance record has been issued.
