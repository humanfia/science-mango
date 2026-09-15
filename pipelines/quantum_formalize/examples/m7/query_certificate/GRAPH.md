flowchart TD
    winner_pass_spec["winner_pass_spec: accepted"]:::accepted
    winner_pass_sound["winner_pass_sound: accepted"]:::accepted
    winner_pass_spec --> winner_pass_sound
    winner_pass_complete["winner_pass_complete: accepted"]:::accepted
    winner_pass_spec --> winner_pass_complete
    presentation_pass_spec["presentation_pass_spec: accepted"]:::accepted
    invalid_rule["invalid_rule: accepted"]:::accepted
    check_sound["check_sound: accepted"]:::accepted
    winner_pass_sound --> check_sound
    presentation_pass_spec --> check_sound
    check_complete["check_complete: accepted"]:::accepted
    winner_pass_complete --> check_complete
    presentation_pass_spec --> check_complete
    check_exact["check_exact: accepted"]:::accepted
    check_sound --> check_exact
    check_complete --> check_exact
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
