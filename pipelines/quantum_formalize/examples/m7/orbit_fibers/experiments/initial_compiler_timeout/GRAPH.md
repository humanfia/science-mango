```mermaid
flowchart TD
    fiber_equiv["fiber_equiv: accepted"]:::accepted
    stabilizer_positive["stabilizer_positive: accepted"]:::accepted
    fiber_count["fiber_count: failed"]:::failed
    fiber_equiv --> fiber_count
    action_count_product["action_count_product: blocked"]:::blocked
    fiber_count --> action_count_product
    orbit_count_div["orbit_count_div: blocked"]:::blocked
    action_count_product --> orbit_count_div
    stabilizer_positive --> orbit_count_div
    orbit_partition["orbit_partition: accepted"]:::accepted
    action_partition["action_partition: accepted"]:::accepted
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
```
