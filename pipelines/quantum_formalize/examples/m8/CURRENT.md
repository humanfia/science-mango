# M8 current status

Updated 2026-09-16T12:58:17.276412+00:00. Full M8 Lean acceptance remains pending.

The SSH-cloned source is frozen: all 35 manifest entries and nine direct dependency hashes were checked. 47 targets in 7 complete batches have passed individual checks, assembly compilation, environment checks, and canonical hash verification.

| Completed batch | Targets |
|---|---:|
| actual_optimizer_resources | 8 |
| anchor | 8 |
| coverage_foundation | 6 |
| cutoff | 8 |
| finite_search | 8 |
| orbit_span | 5 |
| physical_bridge | 4 |

Active work: actual lexicographic discovery, instrumented finite search, raw physical parameters, tagged sequential storage, and explicit admitted/excluded families. The actual three-outcome solver and full root depend on these batches. Component counts do not imply full M8 acceptance.

The M6/M7 canonical proofs are reused through exact source/hash checks. Each proof batch uses gpt-6-astra / medium, two workers, five live attempts, and 600-second compiler calls, within the authorized sixteen-worker ceiling. Late successful drafts are retained; exact local repairs require independent checks and normal replay. The frozen revised M8 is the target; unrestricted all-input M9 is outside this formalization.
