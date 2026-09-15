```mermaid
flowchart TD
    period_control["period_control: accepted"]:::accepted
    literal_progression["literal_progression: accepted"]:::accepted
    period_control --> literal_progression
    bounded_order["bounded_order: accepted"]:::accepted
    period_control --> bounded_order
    literal_progression --> bounded_order
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
```
