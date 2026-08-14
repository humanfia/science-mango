# Ansatz-v3 scientific selector and transition policy

This policy is an opt-in, checkpoint-incompatible fresh campaign. It does not
reinterpret or modify the running ansatz-v3 r4 campaign. Candidate-batch
policies v1--v6 and quota schema v1 retain their historical behavior; only
candidate-batch policy v7 with formal-audit quota schema v2 enables the rules
below.

## Formal-audit allocation

The 72 volume-bound audit slots are unchanged. Across those slots, the policy
requires at least six fresh audits each for support splits `2+2`, `2+3`, and
`3+2`. Within a volume slot, the selector orders candidates by:

1. an unmet support-split minimum;
2. non-quick candidates before the one bounded quick-exploration slot;
3. replayed proof strength (exact, then freshly replayed two-sector lower
   bound, then ordinary/UNKNOWN);
4. undercovered lattice-q and algebraic-mechanism strata;
5. at most one authenticated Reviewer undercoverage focus per round;
6. replayed, X/Z-canonical low-weight negative risk;
7. structural novelty and stable deterministic tie-breaks.

All strata are recomputed from `A_terms`, `B_terms`, and geometry. Reported
mechanism, split, lattice-q, BP/OSD distance, FOM, score, and fitness values are
not selection authority. Volumes 127 and 132 remain mandatory.

## Reviewer authority

Reviewer prose never enters a rank key. A suggestion is eligible only when it
comes from the exact hash-bound `review.json`, has an accepted verdict, is
inside its one-to-three-round horizon, requests `increase`, and names a closed
support-split or algebraic-mechanism enum. It may affect one fresh slot in a
round and cannot outrank a hard split deficit or replayed proof.

## X/Z witness use

Only replayed formal logical witnesses contribute to the negative-risk index.
For BB codes, a verified weight-preserving inversion/block-swap isometry maps Z
witnesses to the canonical X sector before aggregation, avoiding solver-order
X/Z bias. Repeated observations of the same candidate count once. UNKNOWN,
timeouts, corrupt evidence, failed isometry replay, and BP/OSD outputs are
no-vote and give zero positive credit.

## Machine transition gate

The controller rebuilds a self-hashed scientific-progress prefix from sealed
quota reports and formal-audit JSONL. FILLED report strata must agree with the
same-round audited construction. A plateau can request a representation change
only after all of these conditions hold:

- at least 48 fresh terminal audits;
- four consecutive sealed rounds with proven-FOM improvement at most `0.01`;
- all audited candidates are target-negative and no audit is unresolved;
- the three support-split minimums, all five algebraic-mechanism minimums, at
  least 24 distinct lattice-q strata, and mandatory volumes 127 and 132 are
  covered;
- no trusted win exists.

A freshly replayed lower bound of at least 9, or a candidate within three of
its required distance, overrides the plateau and keeps the family in a
targeted-deep-proof state. UNKNOWN never counts as stagnation.

The machine gate may emit `representation_change_required` and atomically stop
the parent. A child can be materialized or launched only from an installed,
hash-bound, proof-compatible template whose parent representation is
compatible. No such post-v3 same-family successor is installed in this change,
so the trigger is automatic but child launch remains fail-closed. Transition
to lifted-product, protograph, or another algebraic family remains manual and
also requires the full finite-domain/Stage-2 family-switch evidence gate.

The parent and child launch bindings conditionally freeze the quota-v2 and
science finite-domain files, the policy-v5 marker, and their exact source
identities. Historical ansatz-v3 quota-v1 transactions keep their original
dependency and invocation shapes.
