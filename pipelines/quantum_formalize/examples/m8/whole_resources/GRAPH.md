flowchart TD
    elementary_bounds["elementary_bounds: accepted"]:::accepted
    original_preprocess_bound["original_preprocess_bound: accepted"]:::accepted
    selected_span["selected_span: accepted"]:::accepted
    projection["projection: accepted"]:::accepted
    charge_length["charge_length: accepted"]:::accepted
    single_calls["single_calls: accepted"]:::accepted
    noLogical_early["noLogical_early: accepted"]:::accepted
    indexed_work_bound["indexed_work_bound: accepted"]:::accepted
    elementary_bounds --> indexed_work_bound
    original_preprocess_bound --> indexed_work_bound
    selected_span --> indexed_work_bound
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
