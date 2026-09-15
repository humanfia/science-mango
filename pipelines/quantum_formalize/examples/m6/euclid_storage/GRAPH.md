flowchart TD
    rem_loop_refines["rem_loop_refines: accepted"]:::accepted
    gcd_loop_refines["gcd_loop_refines: accepted"]:::accepted
    rem_loop_refines --> gcd_loop_refines
    gcd_start_refines["gcd_start_refines: accepted"]:::accepted
    gcd_loop_refines --> gcd_start_refines
    preprocess_refines["preprocess_refines: accepted"]:::accepted
    gcd_start_refines --> preprocess_refines
    rem_loop_safe["rem_loop_safe: accepted"]:::accepted
    rem_loop_refines --> rem_loop_safe
    gcd_loop_safe["gcd_loop_safe: accepted"]:::accepted
    rem_loop_safe --> gcd_loop_safe
    rem_loop_refines --> gcd_loop_safe
    gcd_start_safe["gcd_start_safe: accepted"]:::accepted
    gcd_loop_safe --> gcd_start_safe
    preprocess_safe["preprocess_safe: accepted"]:::accepted
    gcd_start_safe --> preprocess_safe
    gcd_start_refines --> preprocess_safe
    slots_encoding["slots_encoding: accepted"]:::accepted
    control_encoding["control_encoding: accepted"]:::accepted
    control_values_fit["control_values_fit: accepted"]:::accepted
    control_encoding --> control_values_fit
    layout_bound["layout_bound: accepted"]:::accepted
    preprocess_storage["preprocess_storage: accepted"]:::accepted
    preprocess_refines --> preprocess_storage
    preprocess_safe --> preprocess_storage
    slots_encoding --> preprocess_storage
    control_values_fit --> preprocess_storage
    layout_bound --> preprocess_storage
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
