# M8 dependency plan

This is a scope/dependency plan, not a proof receipt. The first three batches can run independently; later batches wait for canonical parent receipts. Up to sixteen proof workers are authorized; current batches use two each.

```mermaid
flowchart TD
  anchor["anchor"]
  cutoff["cutoff"]
  physical_bridge["physical_bridge"]
  finite_search["finite_search"]
  finite_search --> discovery
  discovery["discovery"]
  anchor --> discovery
  cutoff --> discovery
  solver["solver"]
  discovery --> solver
  physical_bridge --> solver
  signed_trace["signed_trace"]
  physical_bridge --> signed_trace
  indexed_resources["indexed_resources"]
  discovery --> indexed_resources
  cutoff --> indexed_resources
  signed_trace --> indexed_resources
  sequential_resources["sequential_resources"]
  indexed_resources --> sequential_resources
  direction_invariant["direction_invariant"]
  anchor --> direction_invariant
  coverage["coverage"]
  solver --> coverage
  direction_invariant --> coverage
  exclusion["exclusion"]
  anchor --> exclusion
  cutoff --> exclusion
  original_m8["original_m8"]
  solver --> original_m8
  sequential_resources --> original_m8
  coverage --> original_m8
  exclusion --> original_m8
```

| Stage | Original obligation |
| --- | --- |
| anchor | Actual anchor presentations and exact equivalence to zero-containing translation presentations |
| cutoff | Fixed cutoff and parameter-free arithmetic envelopes |
| physical_bridge | Actual all-order M6 optimizer, gcd degree and inverse physical witness transport |
| discovery | Lexicographic finite enumeration, first passing tuple, exact failure and actual visited-trial bound |
| solver | Three actual outcomes; NoLogical iff F=1; recognized iff full gcd nontrivial and orbit span within cutoff |
| signed_trace | Actual recurrence coefficient magnitude, bit width, exact division and pinned query interface |
| indexed_resources | Actual discovery, Euclid, trace and witness indexed-bit work and reusable storage |
| sequential_resources | Tagged sequential-store simulation with original n^12 time and n^4 bit-space guarantees |
| direction_invariant | Within-block generated subgroup invariant and proper separated-direction obstruction |
| coverage | All three admitted infinite families, odd/even orders, full multiplicities, diagonal minimum distance and distinct nonproduct claim |
| exclusion | Exact surviving complement; cardinality rejection; power-two antipodal rejected family |
| original_m8 | Complete revised M8 source-bound closed root; no M9 or correctness/cost oracle |

The finite_search sub-batch proves the concrete first-success cursor and its actual callback visit bound before the discovery composition.
