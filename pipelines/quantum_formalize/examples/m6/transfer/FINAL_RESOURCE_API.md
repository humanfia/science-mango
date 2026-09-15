# Original M6 resource integration API

All work and storage functions use the literal indexed scatter, coefficient postprocessing and actual preprocessing definitions. The actual physical weight instances are `M6.ActualTransfer.boundary_indexed_resources` and `character_indexed_resources` in `M6WeightResourcesAccepted` (accepted).

`M6.ActualTransfer.actualDistanceWork N a b` specializes the generic distance counter with `M6.Euclid.preprocessBitCost N a b (M6.Cyclic.modulus N)`. `actualWitnessWork N a b k` uses that same real preprocessing charge and the additional query count returned by the actual solve. The accepted module `M6SolveQueriesAccepted` publishes `M6.ActualTransfer.actual_solve_queries` and proves every actual `solve = some (d,v,k)` has k≤2N, without an oracle premise.

The final work theorems `M6.ActualTransfer.actual_distance_work` and `actual_witness_work` are accepted in `M6SolveResourcesAccepted` with their full actual imported closures. Their original condition is span a b<N; the latter additionally identifies the returned result. Their conclusions are respectively ≤50000*N³*4^span and ≤200000*N⁴*4^span. They have no supplied Euclid cost or query-count assumption.

`M6.ActualTransfer.actualSolveStorage N a b` uses the concrete four-polynomial-slot and sixteen-register layout `M6.EuclidStorage.actualPreprocessStorage N`, plus the paired-query workspace. `actual_solve_storage` is accepted in `M6SolveStorageAccepted`, using the verified Euclid slot-simulation closure; its conclusion is ≤16384*N²*2^span under span<N, with no supplied space estimate.

The actual right-shift/subtraction coefficient loop and scan are independently connected to Q and firstPositive in `postprocessing`. `post_safety` checks their signed coefficient width. Both modules have complete accepted experiment receipts and independent exact-target/axiom audits.

The original bit-operation model charges two window dot computations and local factor evaluation within `128*(R+1)+128` per scatter event, and memory/index manipulations in `16*actualAddressBits`. This allowance concerns the specified actual boundary/character weights. It is not a runtime guarantee for an arbitrary weight function, a Python interpreter or Lean code generation.

The fixed signature/degree, span and two window coefficient arrays are preprocessing data shared by all pinned queries. The work counter charges Euclid once, as in the original indexed-array algorithm; it does not claim a Lean evaluator automatically caches the displayed Q expression. The already proved preprocessing result identifies the cached value with the signature.

`M6RecoveryLayoutAccepted` verifies that the conservative full-coordinate recovery frames fit the unchanged query workspace and that the full solve allocation fits the unchanged address width. Option-bit pins use two bits per coordinate. These are supplementary budget facts, not a compiler execution-stack requirement.
