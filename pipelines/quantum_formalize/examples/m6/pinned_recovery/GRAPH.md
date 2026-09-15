flowchart TD
    weight_bound["weight_bound: accepted"]:::accepted
    agrees_pin["agrees_pin: accepted"]:::accepted
    enumerator_coeff["enumerator_coeff: accepted"]:::accepted
    count_nonnegative_positive["count_nonnegative_positive: accepted"]:::accepted
    count_pin_partition["count_pin_partition: accepted"]:::accepted
    agrees_pin --> count_pin_partition
    decode_unique["decode_unique: accepted"]:::accepted
    distance_spec["distance_spec: accepted"]:::accepted
    first_positive_distance["first_positive_distance: accepted"]:::accepted
    weight_bound --> first_positive_distance
    enumerator_coeff --> first_positive_distance
    count_nonnegative_positive --> first_positive_distance
    distance_spec --> first_positive_distance
    choose_properties["choose_properties: accepted"]:::accepted
    recover_properties["recover_properties: accepted"]:::accepted
    choose_properties --> recover_properties
    recover_positive["recover_positive: accepted"]:::accepted
    recover_from_counts["recover_from_counts: accepted"]:::accepted
    count_nonnegative_positive --> recover_from_counts
    count_pin_partition --> recover_from_counts
    decode_unique --> recover_from_counts
    recover_properties --> recover_from_counts
    recover_positive --> recover_from_counts
    solve_exact["solve_exact: accepted"]:::accepted
    distance_spec --> solve_exact
    first_positive_distance --> solve_exact
    recover_from_counts --> solve_exact
    minimum_witness["minimum_witness: accepted"]:::accepted
    solve_exact --> minimum_witness
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
