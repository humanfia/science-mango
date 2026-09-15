```mermaid
flowchart TD
    period_control["period_control: failed"]:::failed
    literal_progression["literal_progression: blocked"]:::blocked
    period_control --> literal_progression
    bounded_order["bounded_order: blocked"]:::blocked
    period_control --> bounded_order
    literal_progression --> bounded_order
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
```
