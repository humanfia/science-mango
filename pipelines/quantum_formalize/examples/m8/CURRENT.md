# M8 current status

Updated 2026-09-16T13:24:11.093907+00:00. Full M8 Lean acceptance remains pending.

The SSH-cloned source is frozen: all 35 manifest entries and nine direct dependency hashes were checked. 72 targets in 11 complete batches have passed individual checks, assembly compilation, environment checks, and canonical hash verification.

| Completed batch | Targets |
|---|---:|
| actual_optimizer_resources | 8 |
| anchor | 8 |
| coverage_foundation | 6 |
| cutoff | 8 |
| diagonal | 8 |
| finite_search | 8 |
| orbit_span | 5 |
| physical_bridge | 4 |
| raw_parameters | 3 |
| tagged_store | 8 |
| weighted_search | 6 |

Active and pending dependency work is listed in GRAPH.md and final/SCOPE_MAP.md. Component counts do not imply full M8 acceptance. Explicit admitted and rejected families, complete three-outcome semantics, actual cost composition and source-bound root acceptance must all close.

The M6/M7 canonical proofs are reused through exact source/hash checks. Each proof batch uses gpt-6-astra / medium, two workers, five live attempts, and 600-second compiler calls, within the authorized sixteen-worker ceiling. Late successful drafts are retained; exact local repairs require independent checks and normal replay. The frozen revised M8 is the target; unrestricted all-input M9 is outside this formalization.
