flowchart TD
    permutation_weight["permutation_weight: accepted"]:::accepted
    shift_laws["shift_laws: accepted"]:::accepted
    multiply_laws["multiply_laws: accepted"]:::accepted
    conv_shift["conv_shift: accepted"]:::accepted
    conv_multiply["conv_multiply: accepted"]:::accepted
    translated_boundary["translated_boundary: accepted"]:::accepted
    conv_shift --> translated_boundary
    shift_laws --> translated_boundary
    translated_syndrome["translated_syndrome: accepted"]:::accepted
    conv_shift --> translated_syndrome
    multiplied_boundary["multiplied_boundary: accepted"]:::accepted
    conv_multiply --> multiplied_boundary
    multiplied_syndrome["multiplied_syndrome: accepted"]:::accepted
    conv_multiply --> multiplied_syndrome
    exchange_laws["exchange_laws: accepted"]:::accepted
    translated_weight["translated_weight: accepted"]:::accepted
    permutation_weight --> translated_weight
    multiplied_weight["multiplied_weight: accepted"]:::accepted
    permutation_weight --> multiplied_weight
    exchange_weight["exchange_weight: accepted"]:::accepted
    lift_transport["lift_transport: accepted"]:::accepted
    translation_isometry["translation_isometry: accepted"]:::accepted
    lift_transport --> translation_isometry
    shift_laws --> translation_isometry
    translated_boundary --> translation_isometry
    translated_syndrome --> translation_isometry
    translated_weight --> translation_isometry
    multiplier_isometry["multiplier_isometry: accepted"]:::accepted
    lift_transport --> multiplier_isometry
    multiply_laws --> multiplier_isometry
    multiplied_boundary --> multiplier_isometry
    multiplied_syndrome --> multiplier_isometry
    multiplied_weight --> multiplier_isometry
    exchange_isometry["exchange_isometry: accepted"]:::accepted
    lift_transport --> exchange_isometry
    exchange_laws --> exchange_isometry
    exchange_weight --> exchange_isometry
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
