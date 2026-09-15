flowchart TD
    all_sound["all_sound: accepted"]:::accepted
    all_complete["all_complete: accepted"]:::accepted
    all_membership["all_membership: accepted"]:::accepted
    all_sound --> all_membership
    all_complete --> all_membership
    effective_valid["effective_valid: accepted"]:::accepted
    all_membership --> effective_valid
    signature_allowed["signature_allowed: accepted"]:::accepted
    all_membership --> signature_allowed
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
