flowchart TD
    win_membership["win_membership: accepted"]:::accepted
    win_sound_complete["win_sound_complete: accepted"]:::accepted
    win_membership --> win_sound_complete
    finite_extreme["finite_extreme: accepted"]:::accepted
    winning_dominator["winning_dominator: accepted"]:::accepted
    finite_extreme --> winning_dominator
    win_membership --> winning_dominator
    empty_iff["empty_iff: accepted"]:::accepted
    winning_dominator --> empty_iff
    win_membership --> empty_iff
    nonwinner_strict_dominator["nonwinner_strict_dominator: accepted"]:::accepted
    winning_dominator --> nonwinner_strict_dominator
    pareto_laws["pareto_laws: accepted"]:::accepted
    lex_laws["lex_laws: accepted"]:::accepted
    better_laws["better_laws: accepted"]:::accepted
    pareto_laws --> better_laws
    lex_laws --> better_laws
    selector_exact["selector_exact: accepted"]:::accepted
    win_sound_complete --> selector_exact
    empty_iff --> selector_exact
    better_laws --> selector_exact
    selector_strict_dominator["selector_strict_dominator: accepted"]:::accepted
    nonwinner_strict_dominator --> selector_strict_dominator
    better_laws --> selector_strict_dominator
    empty_objectives["empty_objectives: accepted"]:::accepted
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
