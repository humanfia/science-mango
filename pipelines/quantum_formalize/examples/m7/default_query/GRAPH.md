flowchart TD
    sector_modes["sector_modes: accepted"]:::accepted
    noLogical_policy["noLogical_policy: accepted"]:::accepted
    literal_fiber["literal_fiber: accepted"]:::accepted
    winners_exact["winners_exact: accepted"]:::accepted
    invalid_rejection["invalid_rejection: accepted"]:::accepted
    winners_exact --> invalid_rejection
    strict_dominator["strict_dominator: accepted"]:::accepted
    empty_objectives["empty_objectives: accepted"]:::accepted
    presentation_exact["presentation_exact: accepted"]:::accepted
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
