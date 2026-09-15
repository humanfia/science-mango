flowchart TD
    shift_card_anchor["shift_card_anchor: accepted"]:::accepted
    difference_translation["difference_translation: accepted"]:::accepted
    anchored_difference_gcd["anchored_difference_gcd: accepted"]:::accepted
    shift_quotient_polynomial["shift_quotient_polynomial: accepted"]:::accepted
    signature_translation["signature_translation: accepted"]:::accepted
    shift_quotient_polynomial --> signature_translation
    anchored_normalization["anchored_normalization: accepted"]:::accepted
    shift_card_anchor --> anchored_normalization
    difference_translation --> anchored_normalization
    anchored_difference_gcd --> anchored_normalization
    signature_translation --> anchored_normalization
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
