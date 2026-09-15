flowchart TD
    pareto_interval["pareto_interval: accepted"]:::accepted
    lex_interval["lex_interval: accepted"]:::accepted
    pareto_comparisons["pareto_comparisons: accepted"]:::accepted
    lex_comparisons["lex_comparisons: accepted"]:::accepted
    compare_exact["compare_exact: accepted"]:::accepted
    pareto_interval --> compare_exact
    lex_interval --> compare_exact
    compare_bound["compare_bound: accepted"]:::accepted
    pareto_comparisons --> compare_bound
    lex_comparisons --> compare_bound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
