flowchart TD
    address_representation["address_representation: accepted"]:::accepted
    comparison_exact["comparison_exact: accepted"]:::accepted
    read_work["read_work: accepted"]:::accepted
    comparison_exact --> read_work
    write_work["write_work: accepted"]:::accepted
    comparison_exact --> write_work
    write_layout["write_layout: accepted"]:::accepted
    packed_layout["packed_layout: accepted"]:::accepted
    address_representation --> packed_layout
    indexed_read["indexed_read: accepted"]:::accepted
    address_representation --> indexed_read
    comparison_exact --> indexed_read
    indexed_write["indexed_write: accepted"]:::accepted
    address_representation --> indexed_write
    comparison_exact --> indexed_write
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
