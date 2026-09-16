flowchart TD
    distance_work["distance_work: accepted"]:::accepted
    witness_work["witness_work: accepted"]:::accepted
    solve_storage["solve_storage: accepted"]:::accepted
    weight_bounds["weight_bounds: accepted"]:::accepted
    indexed_guarantee["indexed_guarantee: accepted"]:::accepted
    trace_capacity["trace_capacity: accepted"]:::accepted
    weight_bounds --> trace_capacity
    trace_prefix_capacity["trace_prefix_capacity: accepted"]:::accepted
    weight_bounds --> trace_prefix_capacity
    scatter_capacity["scatter_capacity: accepted"]:::accepted
    weight_bounds --> scatter_capacity
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
