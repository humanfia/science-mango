flowchart TD
    decode_encode["decode_encode: accepted"]:::accepted
    encode_decode["encode_decode: accepted"]:::accepted
    four_field_order["four_field_order: accepted"]:::accepted
    realize_decode["realize_decode: accepted"]:::accepted
    domain_univ["domain_univ: accepted"]:::accepted
    leastAction_spec["leastAction_spec: accepted"]:::accepted
    decode_encode --> leastAction_spec
    encode_decode --> leastAction_spec
    realize_decode --> leastAction_spec
    domain_univ --> leastAction_spec
    winning_fiber["winning_fiber: accepted"]:::accepted
    presentation_exact["presentation_exact: accepted"]:::accepted
    leastAction_spec --> presentation_exact
    winning_fiber --> presentation_exact
    presentation_sound["presentation_sound: accepted"]:::accepted
    leastAction_spec --> presentation_sound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
