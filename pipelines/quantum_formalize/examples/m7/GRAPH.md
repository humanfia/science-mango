# Original M7 dependency map

Top-level nodes preserve the original proof obligations. Component receipts and running subgraphs are recorded in graph.json and CURRENT.md; no full-root acceptance is implied.

```mermaid
flowchart TD
    selection["selection: planned"]:::planned
    recipe_action["recipe_action: planned"]:::planned
    support_polynomials["support_polynomials: planned"]:::planned
    recipe_action --> support_polynomials
    signature_transport["signature_transport: planned"]:::planned
    support_polynomials --> signature_transport
    canonicalization["canonicalization: planned"]:::planned
    recipe_action --> canonicalization
    prefix_arithmetic["prefix_arithmetic: planned"]:::planned
    support_polynomials --> prefix_arithmetic
    orbit_prefix["orbit_prefix: planned"]:::planned
    recipe_action --> orbit_prefix
    signature_transport --> orbit_prefix
    compact_generation["compact_generation: planned"]:::planned
    canonicalization --> compact_generation
    prefix_arithmetic --> compact_generation
    orbit_prefix --> compact_generation
    physical_labels["physical_labels: planned"]:::planned
    support_polynomials --> physical_labels
    signature_transport --> physical_labels
    query_locality["query_locality: planned"]:::planned
    recipe_action --> query_locality
    physical_labels --> query_locality
    presentation_decoder["presentation_decoder: planned"]:::planned
    recipe_action --> presentation_decoder
    selection --> presentation_decoder
    selector["selector: planned"]:::planned
    compact_generation --> selector
    physical_labels --> selector
    query_locality --> selector
    selection --> selector
    presentation_decoder --> selector
    replay["replay: planned"]:::planned
    selector --> replay
    resources["resources: planned"]:::planned
    compact_generation --> resources
    orbit_prefix --> resources
    selector --> resources
    original_m7["original_m7: planned"]:::planned
    selector --> original_m7
    replay --> original_m7
    resources --> original_m7
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
```
