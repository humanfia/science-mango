flowchart TD
    support_bounds["support_bounds: accepted"]:::accepted
    pure_weights["pure_weights: accepted"]:::accepted
    logical_pauli_components["logical_pauli_components: accepted"]:::accepted
    quantum_distance_spec["quantum_distance_spec: accepted"]:::accepted
    css_distance_min["css_distance_min: accepted"]:::accepted
    support_bounds --> css_distance_min
    pure_weights --> css_distance_min
    logical_pauli_components --> css_distance_min
    quantum_distance_spec --> css_distance_min
    involution_distance["involution_distance: accepted"]:::accepted
    common_quantum_distance["common_quantum_distance: accepted"]:::accepted
    css_distance_min --> common_quantum_distance
    involution_distance --> common_quantum_distance
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
