# M6 formalization: exact distance by indexed transfer

The source is the [accepted original M6 proof](../../../../research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/PROOF.md). The complete original M6 theorem is now accepted in Lean: `M6.Final.original_m6 : M6.Final.OriginalM6`. [Root acceptance and independent audit](ROOT_ACCEPTANCE.json) record the frozen source, exact proposition and standard axioms.

- [Combined theorem and scope](final/README.md)
- [Compiled full-root proof](final/seal/experiment/AcceptedExperiment.lean)
- [Current status](CURRENT.md)
- [Original scope and final acceptance contract](ROOT_CONTRACT.md)
- [Dependency graph](GRAPH.md)
- [Frozen source reference](SOURCE.json)

The existing retrieval → proof → compile/repair → exact-target acceptance pipeline is used with gpt-6-astra / medium, up to16 ready proof workers and five attempts per target. Mathlib and Physlib are searched separately. Original successful proofs and failed attempts are retained. The dedicated root receipt confirms final combined acceptance; retained failed attempts are historical evidence, not promoted proofs.
