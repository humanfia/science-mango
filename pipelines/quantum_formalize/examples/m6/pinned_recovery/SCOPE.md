# M6 pinned finite enumerators and minimum witness recovery

Source: the complete original M6 proof in research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/PROOF.md, especially §4–5. The source was read in full. This module supplies finite binary-vector and pin semantics shared with the character and transfer modules; it does not assume squarefreeness, odd order, positivity of dimension or nonempty logical space.

Vector m is Fin m → ZMod2. Pins are optional bits; none means free and some b fixes the physical coordinate to b. The integer polynomial enumerator sums X^weight over the finite set L of vectors agreeing with the pins. Its coefficient counts full physical weight, including pinned ones. At the final M6 root L is the exact cycle-minus-boundary set, and the proved trace/character expression is identified with this enumerator.

The 14-node DAG proves weight bounds, pin semantics, exact coefficients, positivity, pin partition, fully assigned uniqueness, first positive coefficient/minimum distance, recursive pin invariants and query bounds, and exact minimum witness recovery. Structural recovery permits repeated coordinate requests and skips coordinates already assigned, so no artificial distinctness premise is required. The actual solve visits List.finRange m, tentatively tests zero, otherwise fixes one, and performs at most m further paired coefficient queries. At m=2N this is exactly the original ≤2N bound.

The generic partitions and exact-polynomial-equality hypotheses occur only in reusable auxiliary theorems. minimum_witness applies the actual finite enumerator with no oracle hypothesis; the final M6 root instantiates solve_exact with its proved transfer equality and cannot leave an oracle-correctness premise in the completed M6 result. No practical runtime superiority, arbitrary-span efficiency, M7 or code classification gate is added.

All definitions and exact target types are checked before the source project is frozen for a normal 16-cap, five-round gpt-6-astra medium experiment with Mathlib+Physlib retrieval and standard exact-target/axiom acceptance. No earlier M5 theorem is assumed by these definitions.
