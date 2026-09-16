```mermaid
flowchart TD
    support_data["support_data: accepted"]:::accepted
    literal_polynomial["literal_polynomial: accepted"]:::accepted
    full_direction["full_direction: accepted"]:::accepted
    support_data --> full_direction
    valid["valid: accepted"]:::accepted
    support_data --> valid
    full_direction --> valid
    polynomial_power["polynomial_power: accepted"]:::accepted
    modulus_power["modulus_power: accepted"]:::accepted
    divides_modulus["divides_modulus: accepted"]:::accepted
    polynomial_power --> divides_modulus
    modulus_power --> divides_modulus
    nontrivial["nontrivial: accepted"]:::accepted
    signature["signature: accepted"]:::accepted
    literal_polynomial --> signature
    divides_modulus --> signature
    nontrivial --> signature
    cutoff_half["cutoff_half: accepted"]:::accepted
    degree_bound["degree_bound: accepted"]:::accepted
    nontrivial --> degree_bound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
```
