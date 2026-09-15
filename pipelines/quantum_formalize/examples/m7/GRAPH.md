# M7 formalization dependency graph

Module gates are plans, not acceptance receipts. Ready proof nodes may use up to16 workers; edges are actual dependency gates. Individual executable graphs freeze exact Lean targets.

```mermaid
graph TD
  recipe_action --> support_polynomials
  support_polynomials --> signature_transport
  recipe_action --> canonicalization
  support_polynomials --> prefix_arithmetic
  recipe_action --> orbit_prefix
  signature_transport --> orbit_prefix
  canonicalization --> compact_generation
  prefix_arithmetic --> compact_generation
  orbit_prefix --> compact_generation
  support_polynomials --> physical_labels
  signature_transport --> physical_labels
  recipe_action --> query_locality
  physical_labels --> query_locality
  recipe_action --> presentation_decoder
  selection --> presentation_decoder
  compact_generation --> selector
  physical_labels --> selector
  query_locality --> selector
  selection --> selector
  presentation_decoder --> selector
  selector --> replay
  compact_generation --> resources
  orbit_prefix --> resources
  selector --> resources
  selector --> original_m7
  replay --> original_m7
  resources --> original_m7
```

The finite selection and actual group foundations can proceed independently. Physical labels reuse the accepted M6 closure; arithmetic prefixes instantiate accepted M5 finite-order counting. No claim of full M7 follows from a generic finite-selector theorem. The full root must discharge every concrete bridge and original replay/no-raw-generation clause.
