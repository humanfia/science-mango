flowchart TD
    two_block_R_count["two_block_R_count: accepted"]:::accepted
    pair_indicator_exact["pair_indicator_exact: accepted"]:::accepted
    arithmetic_indicator_expansion["arithmetic_indicator_expansion: accepted"]:::accepted
    two_block_R_count --> arithmetic_indicator_expansion
    exact_rawA["exact_rawA: accepted"]:::accepted
    arithmetic_indicator_expansion --> exact_rawA
    pair_indicator_exact --> exact_rawA
    rawA_nonnegative_and_positive["rawA_nonnegative_and_positive: accepted"]:::accepted
    exact_rawA --> rawA_nonnegative_and_positive
    period_A_exact["period_A_exact: accepted"]:::accepted
    exact_rawA --> period_A_exact
    rawA_nonnegative_and_positive --> period_A_exact
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
