flowchart TD
    workspace_monotone["workspace_monotone: accepted"]:::accepted
    payload_bound["payload_bound: accepted"]:::accepted
    actual_workspace_fits["actual_workspace_fits: accepted"]:::accepted
    workspace_monotone --> actual_workspace_fits
    address_bits_bound["address_bits_bound: accepted"]:::accepted
    payload_bound --> address_bits_bound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
