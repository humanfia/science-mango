flowchart TD
    actual_order_recovery["actual_order_recovery: accepted"]:::accepted
    actual_residue_recovery["actual_residue_recovery: accepted"]:::accepted
    original_m5["original_m5: accepted"]:::accepted
    actual_order_recovery --> original_m5
    actual_residue_recovery --> original_m5
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
