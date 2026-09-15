flowchart TD
    binary_normalization["binary_normalization: accepted"]:::accepted
    rank_order["rank_order: accepted"]:::accepted
    cancel_drop["cancel_drop: accepted"]:::accepted
    binary_normalization --> cancel_drop
    rank_order --> cancel_drop
    cancel_mod["cancel_mod: accepted"]:::accepted
    remainder_aux_correct["remainder_aux_correct: accepted"]:::accepted
    cancel_drop --> remainder_aux_correct
    cancel_mod --> remainder_aux_correct
    rank_order --> remainder_aux_correct
    remainder_correct["remainder_correct: accepted"]:::accepted
    remainder_aux_correct --> remainder_correct
    rank_order --> remainder_correct
    euclid_aux_correct["euclid_aux_correct: accepted"]:::accepted
    remainder_correct --> euclid_aux_correct
    normalized_gcd["normalized_gcd: accepted"]:::accepted
    binary_normalization --> normalized_gcd
    euclid_correct["euclid_correct: accepted"]:::accepted
    euclid_aux_correct --> euclid_correct
    normalized_gcd --> euclid_correct
    remainder_passes["remainder_passes: accepted"]:::accepted
    euclid_aux_passes["euclid_aux_passes: accepted"]:::accepted
    remainder_passes --> euclid_aux_passes
    euclid_passes["euclid_passes: accepted"]:::accepted
    euclid_aux_passes --> euclid_passes
    scan_cost["scan_cost: accepted"]:::accepted
    dense_cancel["dense_cancel: accepted"]:::accepted
    binary_normalization --> dense_cancel
    dense_rank["dense_rank: accepted"]:::accepted
    dense_injective["dense_injective: accepted"]:::accepted
    remainder_safe["remainder_safe: accepted"]:::accepted
    cancel_drop --> remainder_safe
    euclid_safe["euclid_safe: accepted"]:::accepted
    remainder_safe --> euclid_safe
    remainder_correct --> euclid_safe
    euclid_output_width["euclid_output_width: accepted"]:::accepted
    remainder_correct --> euclid_output_width
    bit_cost_bound["bit_cost_bound: accepted"]:::accepted
    euclid_correct --> bit_cost_bound
    euclid_passes --> bit_cost_bound
    scan_cost --> bit_cost_bound
    euclid_safe --> bit_cost_bound
    preprocess_correct_cost["preprocess_correct_cost: accepted"]:::accepted
    euclid_correct --> preprocess_correct_cost
    euclid_output_width --> preprocess_correct_cost
    bit_cost_bound --> preprocess_correct_cost
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
