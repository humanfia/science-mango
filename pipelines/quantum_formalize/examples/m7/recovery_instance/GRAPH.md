flowchart TD
    count_card["count_card: accepted"]:::accepted
    count_partition["count_partition: accepted"]:::accepted
    count_card --> count_partition
    root_zero["root_zero: accepted"]:::accepted
    count_card --> root_zero
    positive_path["positive_path: accepted"]:::accepted
    count_partition --> positive_path
    fresh_leaf["fresh_leaf: accepted"]:::accepted
    count_card --> fresh_leaf
    positive_path --> fresh_leaf
    insert_good["insert_good: accepted"]:::accepted
    fresh_leaf --> insert_good
    strict_decrease["strict_decrease: accepted"]:::accepted
    fresh_leaf --> strict_decrease
    insert_good --> strict_decrease
    count_card --> strict_decrease
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
