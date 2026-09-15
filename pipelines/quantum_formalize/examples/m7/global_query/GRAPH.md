flowchart TD
    winners_exact["winners_exact: accepted"]:::accepted
    strict_dominator["strict_dominator: accepted"]:::accepted
    winning_classes["winning_classes: accepted"]:::accepted
    winning_fiber["winning_fiber: accepted"]:::accepted
    winners_exact --> winning_fiber
    presentation_sound["presentation_sound: accepted"]:::accepted
    same_class_presentation["same_class_presentation: accepted"]:::accepted
    winning_fiber --> same_class_presentation
    physical_presentation["physical_presentation: accepted"]:::accepted
    same_class_presentation --> physical_presentation
    empty_objectives["empty_objectives: accepted"]:::accepted
    invalid_rejection["invalid_rejection: accepted"]:::accepted
    winners_exact --> invalid_rejection
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
