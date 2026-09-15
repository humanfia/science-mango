# Original M7 dependency map

The colors summarize canonical component receipts recorded in [GRAPH_STATE.json](GRAPH_STATE.json). The final root is still in build/type preflight; complete M7 acceptance is not yet established. Detailed scope and component mappings are in [graph.json](graph.json).

```mermaid
flowchart TD
    selection["selection: accepted"]:::accepted
    recipe_action["recipe_action: accepted"]:::accepted
    support_polynomials["support_polynomials: accepted"]:::accepted
    recipe_action --> support_polynomials
    signature_transport["signature_transport: accepted"]:::accepted
    support_polynomials --> signature_transport
    canonicalization["canonicalization: accepted"]:::accepted
    recipe_action --> canonicalization
    prefix_arithmetic["prefix_arithmetic: accepted"]:::accepted
    support_polynomials --> prefix_arithmetic
    orbit_prefix["orbit_prefix: accepted"]:::accepted
    recipe_action --> orbit_prefix
    signature_transport --> orbit_prefix
    compact_generation["compact_generation: accepted"]:::accepted
    canonicalization --> compact_generation
    prefix_arithmetic --> compact_generation
    orbit_prefix --> compact_generation
    physical_labels["physical_labels: accepted"]:::accepted
    support_polynomials --> physical_labels
    signature_transport --> physical_labels
    query_locality["query_locality: accepted"]:::accepted
    recipe_action --> query_locality
    physical_labels --> query_locality
    presentation_decoder["presentation_decoder: accepted"]:::accepted
    recipe_action --> presentation_decoder
    selection --> presentation_decoder
    selector["selector: accepted"]:::accepted
    compact_generation --> selector
    physical_labels --> selector
    query_locality --> selector
    selection --> selector
    presentation_decoder --> selector
    replay["replay: accepted"]:::accepted
    selector --> replay
    resources["resources: accepted"]:::accepted
    compact_generation --> resources
    orbit_prefix --> resources
    selector --> resources
    original_m7["original_m7: running"]:::running
    selector --> original_m7
    replay --> original_m7
    resources --> original_m7
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
```
