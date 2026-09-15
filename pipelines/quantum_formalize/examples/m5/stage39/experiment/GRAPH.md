flowchart TD
    physical_implies_A_positive["physical_implies_A_positive: accepted"]:::accepted
    positive_bounded_progression["positive_bounded_progression: accepted"]:::accepted
    global_occurrence_criterion["global_occurrence_criterion: accepted"]:::accepted
    physical_implies_A_positive --> global_occurrence_criterion
    positive_bounded_progression --> global_occurrence_criterion
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
