flowchart TD
    anchored_enumeration["anchored_enumeration: accepted"]:::accepted
    reduced_polynomial["reduced_polynomial: accepted"]:::accepted
    reduced_connectivity["reduced_connectivity: accepted"]:::accepted
    signature_restriction["signature_restriction: accepted"]:::accepted
    physical_to_residue["physical_to_residue: accepted"]:::accepted
    anchored_enumeration --> physical_to_residue
    reduced_polynomial --> physical_to_residue
    reduced_connectivity --> physical_to_residue
    signature_restriction --> physical_to_residue
    period_necessity["period_necessity: accepted"]:::accepted
    physical_to_residue --> period_necessity
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
