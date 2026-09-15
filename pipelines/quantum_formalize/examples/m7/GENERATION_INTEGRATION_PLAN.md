# Actual compact generation: downstream contract

Preparation only; this document is not a Lean acceptance receipt. The original M7 goal is unchanged.

## Concrete recurrence

Use the arithmetic initial residual root count converted to Nat as fuel. The production state contains only the canonical bases and emitted records. On each call evaluate the actual arithmetic residual at the empty prefix once. If it is zero, return immediately. Otherwise compute one `DescentTrace.trace` using the same actual arithmetic residual, obtain the leaf prefix through `endpoint`, decode the two selected supports, canonicalize the leaf, store its actual realizer and signatures, and recurse after inserting that canonical value. The trace performs two child evaluations per depth step; no second recovery computation occurs. Semantic completion sets are used only in proofs.

Fuel-zero is an explicit total-definition branch. Correctness must show that an admissible call with fuel at least the actual remaining cardinality reaches that branch only with zero residual. It must not silently return incomplete output. The initial arithmetic count/cardinality theorem establishes the bound. Every positive iteration removes at least one remaining element, preserving enough fuel. This is the finite-fuel implementation already allowed by COMPACT_INTEGRATION_PLAN, rather than an extra termination requirement.

## Required proof interfaces

1. Actual recovery returns a full-length prefix whose decoded leaf is in the original root completion set and outside all stored orbits.
2. Its canonical value is fresh, normalized and class-valid. The actual canonical realizer transports the stored leaf to it; the inverse recovers the leaf.
3. Inserting it strictly decreases actual root residual converted to Nat, preserves nonnegativity and the stored invariant, and extends covered orbits.
4. Induction on fuel proves final root residual zero, inclusion of previous bases, and a list of distinct newly emitted canonical values.
5. The emitted records form the final indexed family. Zero residual plus the separately checked raw anchoring bridge proves complete coverage of all requested structural orbits. The final global-query and certificate theorems then receive this family, with their completeness and separation premises discharged.

## Original accounting

For H emitted classes and m = 2(N-1), generation makes H+1 root residual evaluations and exactly 2mH child residual evaluations: T0 = 1 + H(2m+1). Each residual evaluates at most H stored-class factorized counts, giving at most H*T0 such evaluations. Charge actual full-stabilizer computation and storage separately according to the original proof. No raw-support scan, orbit member cache, or full prefix trie is introduced. Optional full path transcripts are explicitly outside the original base-cache bound; do not identify their storage with O(HN). Expanded output is also separately charged.

The final replay must check these actual paths/counts, canonical records, M6 distance witnesses and global query certificates. Generic list-length identities alone do not close the original resource or replay gates.
