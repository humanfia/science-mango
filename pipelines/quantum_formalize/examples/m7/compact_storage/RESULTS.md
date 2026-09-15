# Compact storage bit representation

All seven frozen targets passed normal harness acceptance, exact target and axiom checks, combined assembly and unchanged-environment gates. The actual emission satisfies its field-consistency predicate. Its compact core (all fields except optional full path) has an injective finite-bit encoding of exact layout12N+4≤16N bits. Optional unit-indexed complete-signature tables take totient(N)*(N+1) bits each and recover the actual unit-image signatures, giving≤16HN+2H*totient(N)*N total bits. This does not claim host Lean object bytes or include complete prefix/transcript paths in the compact bound.

Run: `/home/jing/m7-lean-compact-storage-formalization/.humanize-formal-runs/compact_storage-wl3x_rp2/experiment`. Accepted attempts: {'emission_valid': 1, 'field_bounds': 1, 'polynomial_injective': 1, 'storage_bounds': 1, 'support_value_injective': 1, 'encode_core': 4, 'unit_table_recovery': 1}. Full canonical artifacts are in experiment/.
