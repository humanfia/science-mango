flowchart TD
    completion_word_split["completion_word_split: accepted"]:::accepted
    completion_prefix_card["completion_prefix_card: accepted"]:::accepted
    completion_word_split --> completion_prefix_card
    prefix_algebra["prefix_algebra: accepted"]:::accepted
    completion_feasible["completion_feasible: accepted"]:::accepted
    completion_word_split --> completion_feasible
    prefix_algebra --> completion_feasible
    oracle_prefix_count["oracle_prefix_count: accepted"]:::accepted
    completion_prefix_card --> oracle_prefix_count
    completion_feasible --> oracle_prefix_count
    oracle_initial["oracle_initial: accepted"]:::accepted
    oracle_partition_terminal["oracle_partition_terminal: accepted"]:::accepted
    oracle_prefix_count --> oracle_partition_terminal
    recovery_correct["recovery_correct: accepted"]:::accepted
    oracle_initial --> recovery_correct
    oracle_partition_terminal --> recovery_correct
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
