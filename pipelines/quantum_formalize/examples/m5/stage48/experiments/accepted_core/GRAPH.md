flowchart TD
    period_and_order["period_and_order: accepted"]:::accepted
    normalization["normalization: accepted"]:::accepted
    global_birth_later["global_birth_later: accepted"]:::accepted
    core["core: accepted"]:::accepted
    period_and_order --> core
    normalization --> core
    global_birth_later --> core
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
