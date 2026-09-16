flowchart TD
    actual_prefix_charge["actual_prefix_charge: accepted"]:::accepted
    sequential_bound["sequential_bound: accepted"]:::accepted
    actual_prefix_charge --> sequential_bound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
