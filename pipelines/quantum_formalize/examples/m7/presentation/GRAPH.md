flowchart TD
    record_eta["record_eta: accepted"]:::accepted
    record_mono["record_mono: accepted"]:::accepted
    candidates_sound["candidates_sound: accepted"]:::accepted
    candidate_dominates["candidate_dominates: accepted"]:::accepted
    record_eta --> candidate_dominates
    record_mono --> candidate_dominates
    leastOf_spec["leastOf_spec: accepted"]:::accepted
    factorLeast_spec["factorLeast_spec: accepted"]:::accepted
    leastOf_spec --> factorLeast_spec
    candidates_sound --> factorLeast_spec
    candidate_dominates --> factorLeast_spec
    factorLeast_none["factorLeast_none: accepted"]:::accepted
    leastOf_spec --> factorLeast_none
    candidate_dominates --> factorLeast_none
    candidates_sound --> factorLeast_none
    domain_membership["domain_membership: accepted"]:::accepted
    record_eta --> domain_membership
    targetLeast_spec["targetLeast_spec: accepted"]:::accepted
    factorLeast_spec --> targetLeast_spec
    factorLeast_none --> targetLeast_spec
    domain_membership --> targetLeast_spec
    winning_fiber["winning_fiber: accepted"]:::accepted
    presentation_exact["presentation_exact: accepted"]:::accepted
    targetLeast_spec --> presentation_exact
    winning_fiber --> presentation_exact
    presentation_sound["presentation_sound: accepted"]:::accepted
    targetLeast_spec --> presentation_sound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
