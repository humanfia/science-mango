# Actual compact recurrence correctness

Pending canonical `compact_core` and `recovery_instance`. This is a dependency plan, not accepted formalization.

The actual production functions are frozen in `compact_core/lean/M7CompactGeneration.lean`. They use the original arithmetic residual directly, generate a path once, save the actual leaf/canonical/action/signatures/full stabilizer, and pass the next arithmetic root count to the recursive call. The top-level generator computes the initial root count once and uses its Nat value as fuel. No change to those definitions is needed for correctness.

Planned exact connections:

1. `CompactGeneration.residual` equals `RecoveryInstance.count` by unfolding the actual same arithmetic definitions. Emission path, leaf, representative and inserted bases likewise match the accepted recovery interface.
2. If an internal cached root equals the actual residual on entry, the returned cached residual equals the actual residual of its final bases. Every recursive call computes that next root explicitly.
3. Actual recovery preserves GoodBases and gives freshness for each positive step. Induction proves GoodBases of the final bases and pairwise distinct emitted canonical values, disjoint from the initial stored bases.
4. Given valid sectors, GoodBases, a correct root cache and fuel at least its Nat value, induction using the actual strict decrease proves final residual zero and no positive fuel exhaustion. At fuel zero, nonnegativity and the fuel inequality force root zero. No branch is accepted merely because its fuel ran out.
5. Every emitted leaf lies in the original root completion set and realizes its stored representative; the final zero residual proves anchored coverage. Raw coverage is supplied by the separate actual translation/anchoring bridge.
6. Specialize to empty initial bases and the actual initial count. The final stored bases are exactly the fold of emitted canonical values. Their cardinality equals the emission length. This yields the complete structural family used by the existing global-query and finite-certificate checker.

Only internal lemmas may assume the cache/invariant/fuel relation. The public generator correctness theorem must discharge every such premise from its concrete initial call. The final M7 theorem retains the original N≥1, 1≤w≤N and explicit invalid-sector handling; this plan adds no stronger scope or efficiency gate.
