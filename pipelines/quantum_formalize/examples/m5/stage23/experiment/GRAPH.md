flowchart TD
    residual_factors_regular["residual_factors_regular: accepted"]:::accepted
    conditional_indicator["conditional_indicator: accepted"]:::accepted
    residual_factors_regular --> conditional_indicator
    exact_signature_indicator["exact_signature_indicator: accepted"]:::accepted
    conditional_indicator --> exact_signature_indicator
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
