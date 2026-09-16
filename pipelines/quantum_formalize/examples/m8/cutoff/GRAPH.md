flowchart TD
    limit_bounds["limit_bounds: accepted"]:::accepted
    bit_length_limit["bit_length_limit: accepted"]:::accepted
    state_bound["state_bound: accepted"]:::accepted
    limit_bounds --> state_bound
    state_square["state_square: accepted"]:::accepted
    state_bound --> state_square
    indexed_work_envelopes["indexed_work_envelopes: accepted"]:::accepted
    state_square --> indexed_work_envelopes
    indexed_storage_envelope["indexed_storage_envelope: accepted"]:::accepted
    state_bound --> indexed_storage_envelope
    coefficient_capacity["coefficient_capacity: accepted"]:::accepted
    limit_bounds --> coefficient_capacity
    anchor_trial_envelope["anchor_trial_envelope: accepted"]:::accepted
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
