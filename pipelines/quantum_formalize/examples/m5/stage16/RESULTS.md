# Stage 16 result

All six exact frozen targets passed individual Lean compilation, independent target/axiom verification and combined assembly. The frozen project environment remained unchanged. The accepted artifact is [experiment/result.json](experiment/result.json); [experiment/MANIFEST.json](experiment/MANIFEST.json) hashes its 139 evidence files.

This establishes the multiplicity-sensitive exact-signature criterion: for positive N and monic F dividing a, b and the cyclic modulus, the complete signature equals F exactly when no residual irreducible p has F*p dividing both a and b. The final equivalent predicate ranges over the finite normalized-factor set of the quotient. F and the cyclic modulus may have repeated factors; no squarefree, anchored or odd-N restriction was added.

The initial run accepted three nodes and failed only at a namespace lookup in strict_divisor_extra_factor. The first replay qualified the accepted M5.Signature.binary_dvd_antisymm declaration and accepted that fourth target. The exact criterion then required explicit gcd-divisor arguments to avoid metavariable elaboration timeouts, the correct nonunit API, and the coefficient simp lemmas already used by the accepted upstream cyclic-modulus proof. The final finite-factor criterion passed its first live attempt. Targets and assumptions were unchanged throughout.

The final run independently rechecked all six nodes with one attempt each; five drafts were replayed or repaired, and the final node used gpt-6-astra at medium effort. Identical initial queries replayed hash-verified successful Mathlib/Physlib receipts, with fresh searches available for new queries. [FINAL_REPAIR_REPLAY.json](FINAL_REPAIR_REPLAY.json) records this provenance; the preceding runs are retained under experiments, including the rejected coefficient candidate omitted from its exception receipt.

Accepted component proofs do not by themselves establish the polynomial inclusion-exclusion count or full M5. Those remain dependent integration obligations.
