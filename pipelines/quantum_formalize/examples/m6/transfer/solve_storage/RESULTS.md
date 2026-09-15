# Actual solve storage accepted

`M6.ActualTransfer.actual_solve_storage` passed on the first model attempt. The exact original target proves `actualSolveStorage N a b ≤ 16384*N^2*2^(span a b)` under `span a b < N`, with `[NeZero N]`. It supplies no free storage or oracle premise.

The concrete storage function combines the accepted four-polynomial-slot and sixteen-control-register Euclid preprocessing layout with the paired-query indexed-array workspace. The imported Euclid closure proves actual slot simulation and all intermediate width safety, in addition to its allocation bound.

Canonical evidence is in `experiment`: node acceptance, combined assembly acceptance, unchanged environment and experiment success all hold. `AUDIT.json` independently verifies the exact frozen target, submitted candidate, portable declaration, original target/proof olean hashes and allowed axioms (`propext`, `Classical.choice`, `Quot.sound`). `experiment/MANIFEST.json` records all 27 evidence files. The component receipt's legacy `m5_formalized: false` does not evaluate the final M6 root.

Accepted module: `lean/M6SolveStorageAccepted.lean`. The frozen source and statement are unchanged; all dependency gates are resolved. Final global M6 synthesis remains the parent root's separate acceptance task.
