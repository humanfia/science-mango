flowchart TD
    packed_repair_hypotheses["packed_repair_hypotheses: accepted"]:::accepted
    repaired_support_properties["repaired_support_properties: accepted"]:::accepted
    bounded_connected_construction["bounded_connected_construction: accepted"]:::accepted
    packed_repair_hypotheses --> bounded_connected_construction
    repaired_support_properties --> bounded_connected_construction
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
