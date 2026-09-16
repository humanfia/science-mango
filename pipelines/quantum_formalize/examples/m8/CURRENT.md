# M8 current status

Updated 2026-09-16T14:33:27.857071+00:00. Full M8 Lean acceptance remains pending.

The SSH-cloned source is frozen: all 35 manifest entries and nine direct dependency hashes were checked. 169 targets in 24 complete batches have passed individual checks, assembly compilation, environment checks, and canonical hash verification.

| Completed batch | Targets |
|---|---:|
| actual_optimizer_resources | 8 |
| anchor | 8 |
| antipodal_family | 11 |
| bank_layout | 4 |
| coverage_foundation | 6 |
| cutoff | 8 |
| diagonal | 8 |
| diagonal_polynomial | 5 |
| discovery | 10 |
| discovery_resources | 10 |
| exclusion_geometry | 9 |
| finite_search | 8 |
| mixed_family | 8 |
| mixed_nonproduct | 5 |
| orbit_span | 5 |
| p3_family | 8 |
| p4_family | 8 |
| p4_gcd | 6 |
| physical_bridge | 4 |
| raw_parameters | 3 |
| sequential_store | 4 |
| solver | 9 |
| tagged_store | 8 |
| weighted_search | 6 |

Active and pending dependency work is listed in GRAPH.md and final/SCOPE_MAP.md. Component counts do not imply full M8 acceptance. Explicit admitted and rejected families, complete three-outcome semantics, actual cost composition and source-bound root acceptance must all close.

The M6/M7 canonical proofs are reused through exact source/hash checks. Each proof batch uses gpt-6-astra / medium, two workers, five live attempts, and 600-second compiler calls, within the authorized sixteen-worker ceiling. Late successful drafts are retained; exact local repairs require independent checks and normal replay. The frozen revised M8 is the target; unrestricted all-input M9 is outside this formalization.
