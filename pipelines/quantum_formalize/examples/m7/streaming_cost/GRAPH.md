flowchart TD
    cursor_projection["cursor_projection: accepted"]:::accepted
    cursor_bound["cursor_bound: accepted"]:::accepted
    record_projection["record_projection: accepted"]:::accepted
    cursor_projection --> record_projection
    record_bound["record_bound: accepted"]:::accepted
    cursor_bound --> record_bound
    index_projection["index_projection: accepted"]:::accepted
    cursor_projection --> index_projection
    record_projection --> index_projection
    index_bound["index_bound: accepted"]:::accepted
    cursor_bound --> index_bound
    record_bound --> index_bound
    stream_projection_bound["stream_projection_bound: accepted"]:::accepted
    index_projection --> stream_projection_bound
    index_bound --> stream_projection_bound
    scan_bound["scan_bound: accepted"]:::accepted
    stream_projection_bound --> scan_bound
    index_bound --> scan_bound
    record_cardinality["record_cardinality: accepted"]:::accepted
    classDef accepted fill:#dcfce7,stroke:#166534
    classDef running fill:#dbeafe,stroke:#1d4ed8
    classDef planned fill:#f3f4f6,stroke:#6b7280,stroke-dasharray:5 5
    classDef failed fill:#fee2e2,stroke:#991b1b
    classDef blocked fill:#ffedd5,stroke:#9a3412
