# Stage 7 results — exact binary character identities

All five corrected frozen targets passed Lean acceptance and combined compilation. Direct kernel computation closed the two finite bit identities; the full orthogonality identity for arbitrary dimension needed two attempts; other retry targets passed on their first attempts.

The proof covers D=0 and gives the precise character-sum formula for the cardinality of a fibre of any finite vector-valued map, after multiplication by 2^D. It does not yet identify polynomial quotient coordinates or establish the subset generating polynomial and complete signature counts.

The initial run's accepted bit_add is preserved, alongside failed numeric simplification and malformed-binder diagnostics. REPAIR.md explains the initial preflight mismatch and the exact-JSON regeneration fix. No mathematical statement was strengthened or weakened.

[Accepted assembly](experiment/AcceptedExperiment.lean), [acceptance receipt](experiment/result.json), [initial run](experiments/initial_failure/result.json).
