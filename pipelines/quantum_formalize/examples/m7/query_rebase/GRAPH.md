flowchart TD
    reparameterization["reparameterization: accepted"]:::accepted
    realize_reparam["realize_reparam: accepted"]:::accepted
    sector_base["sector_base: accepted"]:::accepted
    feasible_objective["feasible_objective: accepted"]:::accepted
    realize_reparam --> feasible_objective
    sector_base --> feasible_objective
    winners_reparam["winners_reparam: accepted"]:::accepted
    reparameterization --> winners_reparam
    feasible_objective --> winners_reparam
    winning_classes["winning_classes: accepted"]:::accepted
    winners_reparam --> winning_classes
    reparameterization --> winning_classes
    winner_images["winner_images: accepted"]:::accepted
    winners_reparam --> winner_images
    realize_reparam --> winner_images
    reparameterization --> winner_images
    presentation_images["presentation_images: accepted"]:::accepted
    winner_images --> presentation_images
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
