flowchart TD
    raw_realizable["raw_realizable: accepted"]:::accepted
    index_feasible["index_feasible: accepted"]:::accepted
    winner_exact["winner_exact: accepted"]:::accepted
    raw_realizable --> winner_exact
    index_feasible --> winner_exact
    raw_output["raw_output: accepted"]:::accepted
    winner_exact --> raw_output
    raw_realizable --> raw_output
    presentation_exact["presentation_exact: accepted"]:::accepted
    raw_output --> presentation_exact
    winner_exact --> presentation_exact
    empty_exact["empty_exact: accepted"]:::accepted
    raw_realizable --> empty_exact
    index_feasible --> empty_exact
    strict_dominator["strict_dominator: accepted"]:::accepted
    raw_realizable --> strict_dominator
    index_feasible --> strict_dominator
    winner_exact --> strict_dominator
    invalid_rejection["invalid_rejection: accepted"]:::accepted
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
