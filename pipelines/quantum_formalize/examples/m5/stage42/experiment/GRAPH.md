flowchart TD
    prefix_gcd_divisibility["prefix_gcd_divisibility: accepted"]:::accepted
    selected_R_pair_count["selected_R_pair_count: accepted"]:::accepted
    pair_indicator_exact["pair_indicator_exact: accepted"]:::accepted
    prefix_gcd_divisibility --> pair_indicator_exact
    arithmetic_indicator_expansion["arithmetic_indicator_expansion: accepted"]:::accepted
    prefix_gcd_divisibility --> arithmetic_indicator_expansion
    selected_R_pair_count --> arithmetic_indicator_expansion
    exact_conditionalA["exact_conditionalA: accepted"]:::accepted
    pair_indicator_exact --> exact_conditionalA
    arithmetic_indicator_expansion --> exact_conditionalA
    period_conditionalA_exact["period_conditionalA_exact: accepted"]:::accepted
    exact_conditionalA --> period_conditionalA_exact
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
