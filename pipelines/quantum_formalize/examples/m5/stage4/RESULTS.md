# Stage 4 results — quotient cardinality and period bound

Both frozen targets passed Lean acceptance and assembled compilation. Together with stages 1–3, 25 individual lemmas have been accepted.

For monic binary F, Nat.card (AdjoinRoot F) = 2^F.natDegree. For the original signature domain this gives t(F) ≤ 2^F.natDegree. Degree zero and F=1 are included. Imported finite-quotient proof provenance is in DEPENDENCY_IMPORT.json.

Executable period search and the remaining M5 counting and reconstruction obligations remain open in Lean.

[Assembled proof](experiment/AcceptedExperiment.lean), [acceptance receipt](experiment/result.json), [status DAG](experiment/GRAPH.md).
