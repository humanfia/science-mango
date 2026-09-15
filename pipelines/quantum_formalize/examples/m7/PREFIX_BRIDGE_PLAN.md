# Actual M5 prefix arithmetic to original M7

Planning only; no new theorem is marked accepted. Original M7 requires actual finite arithmetic counts, not an assumed counting oracle or raw support-pair enumeration. M5 stage48 contains accepted `M5.ConditionalCount.exact_completion_C`, equating actual Mobius/character/subset-coefficient `completionC` with the cardinality of valid anchored completions. Its `completion_nonnegative_and_exists` already supplies positivity/existence. The four source files listed below were checked against the canonical M5 stage48 manifest before this interface review.

## Exact inherited API

`completionC N w F A B WA WB` uses the selected sets A/B and undecided sets WA/WB; it is zero if either selected cardinality exceeds w. `rawCompletion` sums the arithmetic Mobius weight over divisors of the selected support gcd and polynomial exclusion subsets, multiplying two actual `nSelected` character counts. `validCompletions` is a proof specification; it must not become the M7 generation algorithm.

`exact_completion_C` assumes N>0, F monic, F divides the full cyclic modulus, and `PrefixOK`: zero selected in both blocks, selected/undecided positions within range N, selected and undecided disjoint per block, and selected cardinalities at most w. No odd-N or squarefree assumption is present. `M5.BinaryRecovery.recover` already implements zero-first positive descent and has accepted length/positivity/correctness theorems conditional on count partition and the full-length leaf rule.

## Remaining actual connections

1. Define finite sector arithmetic `C_E = sum F in E, completionC ...`, using a Finset of monic full divisors, so duplicate F values are impossible. Prove actual completion classes for distinct F are disjoint. Derive equality with the cardinality of the union, nonnegativity and positive iff a queried completion exists. Do not replace C_E by that cardinality in its definition.
2. Supply an extended prefix-validity wrapper allowing overfull selections. Such branches are zero by the actual arithmetic definition and by impossible final cardinality. This is necessary because a selected child can exceed w even when its parent obeys PrefixOK; do not quietly omit that branch.
3. Prove the actual zero/one child partition by removing the next undecided position, and selecting it only in the one child. Preserve the anchored zero positions. At full depth prove a 0/1 leaf count for the actual connected, weight-w, full-signature-in-E recipe.
4. Bridge bounded natural support exponents to M7 Finset(ZMod N) using the injective val/cast correspondence, and the accepted support-polynomial and domain identities. Reconcile M5 completeSignature with the literal M6/M7 gcd definition. This must be a proved equality, not an unverified abbreviation assumption.
5. Instantiate the accepted M5 descent theorem with actual residual arithmetic C_E minus the full-stabilizer orbit counts. Prove nonnegative residual, prefix partition and leaf exclusion from already emitted distinct canonical classes. Only then recover a new orbit representative. Complete termination and call bounds belong to compact_generation/resources.

These interfaces preserve the original symbolic constructive-selector gate. They add no practical efficiency, M8, extraction or raw-scan implementation obligation.

## Verified source identities

- `../m5/stage48/lean/M5ConditionalCount.lean`: `33c41a184d072c835fdc4923f9a244f89d9d1b755eef72785be85cc44f63c72d`
- `../m5/stage48/lean/M5ConditionalCountAccepted.lean`: `bd2b68c6d8df1d36633d3a179aaafe6ff8ae4eef64053c55f7a37e147edfd86d`
- `../m5/stage48/lean/M5BinaryRecovery.lean`: `67f8319e2f68e5a7119ad880bc4de0f11c17f998bc581bb41e6e6e075b810e68`
- `../m5/stage48/lean/M5BinaryRecoveryAccepted.lean`: `5d21a1367fc74d0fe199cfc6bf8327a7f21c435f72aaba48fe28b20ed8cd9673`
