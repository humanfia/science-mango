# Source-to-formal-proof chain

This is a status map of the original reviewed proof, not a strengthened theorem or a completion percentage. Exact source: [PROOF.md](../../../../research/quantum_m5/research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md). For frozen target statements and acceptance receipts, follow the batch links. A successful identity is retained even while a larger source section remains incomplete.

| Original component | Formal status | Evidence / next dependency |
|---|---|---|
| §1 finite quotient period law and bound | Period law, bound and exact finite period search accepted | [stage3](stage3/RESULTS.md), [stage12](stage12/RESULTS.md), [stage45](stage45/RESULTS.md) |
| §2 explicit subset n formula | Exact identity, integer division and nonnegativity accepted | [stage20](stage20/RESULTS.md) |
| §2 explicit repeated-tuple R formula | Exact identity, integer division and nonnegativity accepted | [stage24](stage24/RESULTS.md) |
| §3 integer connectivity indicator | Accepted | [stage9](stage9/RESULTS.md) |
| §3 polynomial exact-signature exclusion | Finite Boolean exclusion and factor products accepted; Exact finite factor-subset signature indicator accepted | [stage17](stage17/RESULTS.md), [stage18](stage18/RESULTS.md), [stage16](stage16/RESULTS.md) → stage23 |
| §3 anchored C and conditional recovery | Exact C and conditional formula accepted; actual recovery connection open | [stage27](stage27/RESULTS.md); [stage34](stage34/RESULTS.md); actual recovery connection stage46 remains |
| §4 feasible-pattern A, necessity and recovery | Exact A, conditional formula and necessity accepted; actual recovery connection open | [stage31](stage31/RESULTS.md), [stage35](stage35/RESULTS.md), [stage42](stage42/RESULTS.md); actual recovery stage47 remains |
| §4–5 global arithmetic existence criterion | Accepted, including bounded source and infinite progression | [stage39](stage39/RESULTS.md) |
| §5 packing and signature preservation | Accepted components | [stage6](stage6/RESULTS.md), [stage8](stage8/RESULTS.md), [stage21](stage21/RESULTS.md) |
| §5 actual bounded connected support construction | Accepted | stage19 + stage21 → stage22 |
| §5 literal-support progression and bounded physical order | Accepted | stage12 + earlier bounded progression → stage25; combine with stage22 |
| §6 bounded exact birth and all later-order decisions | Actual first birth and arbitrary later-order classification accepted; recipe recovery connection open | [stage43](stage43/RESULTS.md); actual recovery stage46 remains |
| §1 weight-one boundary and final arithmetic procedure | Weight-one accepted; final procedure integration open | Boundary theorem and full correctness/termination integration |

```mermaid
flowchart TD
  n[stage20: exact n — accepted] --> anchor[stage26: anchored block count — accepted]
  R[stage24: exact R — accepted] --> A[stage31: exact A — accepted; recovery open]
  int[stage9: integer indicator — accepted] --> C[stage27: exact C — accepted; recovery open]
  crit[stage16: polynomial criterion — accepted] --> pie[stage23: exact polynomial indicator — accepted]
  finite[stage17 + 18: finite exclusion / products — accepted] --> pie
  pie --> C
  pie --> A
  int --> A
  anchor --> C
  pack[stage19 + 21: packing repair ingredients — accepted] --> construct[stage22: connected support construction — accepted]
  period[stage3 + 12: period and lift — accepted] --> orders[stage25: actual progression and bounded order — accepted]
  construct --> bounded[stage28: feasible pattern to bounded physical source — accepted]
  orders --> bounded
  A --> global[stage39: global realizability criterion — accepted]
  bounded --> global
  C --> final[Original M5 arithmetic workflow — open]
  global --> final
```

The scheduler only releases proved dependencies. Independent ready nodes may run in parallel; the configured proof-worker ceiling is16. The final root must connect the finite arithmetic definitions to the structurally terminating actual recovery procedures; assumed oracle correctness is insufficient. Generated Lean runtime code is not an additional acceptance requirement. No distance, inherited-intersection, or anchored-sorting goal is added.
