# M6 formalization: exact distance by indexed transfer

The source is the [accepted original M6 proof](../../../../research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/PROOF.md). Natural-language acceptance is already recorded; Lean formalization is in progress, not complete.

- [Current status](CURRENT.md)
- [Original scope and final acceptance contract](ROOT_CONTRACT.md)
- [Dependency graph](GRAPH.md)
- [Frozen source reference](SOURCE.json)

The existing retrieval → proof → compile/repair → exact-target acceptance pipeline is used with gpt-6-astra / medium, up to16 ready proof workers and five attempts per target. Mathlib and Physlib are searched separately. Original successful proofs and failed attempts are retained. Component success does not establish the final M6 theorem.
