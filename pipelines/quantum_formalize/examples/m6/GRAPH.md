# M6 proof dependency graph

Independent first modules run concurrently; dependent targets run only after accepted proof imports. Module gates below are planned, not proof receipts.

```mermaid
graph TD
  cyclic_algebra --> physical_coordinates
  cyclic_algebra --> kernel_fibers
  physical_coordinates --> kernel_fibers
  physical_coordinates --> dual_involution
  transfer_walks --> transfer_trace
  character_orthogonality --> character_pins
  pinned_finite_enumeration --> character_pins
  kernel_fibers --> normalized_enumerators
  dual_involution --> normalized_enumerators
  transfer_trace --> normalized_enumerators
  character_pins --> normalized_enumerators
  pinned_finite_enumeration --> minimum_recovery
  normalized_enumerators --> minimum_recovery
  dual_involution --> css_distance
  minimum_recovery --> css_distance
  transfer_trace --> resource_bounds
  minimum_recovery --> resource_bounds
  resource_bounds --> fixed_span_improvement
  physical_coordinates --> symmetry_edges
  normalized_enumerators --> symmetry_edges
  css_distance --> original_m6
  resource_bounds --> original_m6
  fixed_span_improvement --> original_m6
  symmetry_edges --> original_m6
```

The cyclic, transfer, character and pinned-enumeration roots are independent. Resource accounting starts from the actual transfer recurrence and joins witness-query bounds. Final acceptance waits for every original-scope branch.
