# M7 compact coverage: eliminate expanded raw-pair storage
Current follow-up, 2026-09-15. Finish original M7 with the same harness.
M5 and M6 are adopted at their stated strengths; M8 is not a prerequisite.

## Why this follow-up is necessary
The first M7 generation draft chooses one new class per completed branch,
but then explicitly materializes its whole anchored orbit. Across all
classes this can materialize every valid anchored pair. The current user
requires original M7 "without raw scan"; do not dismiss this distinction
with a change of vocabulary. Prove the following stronger counting method,
which stores canonical representatives rather than all orbit members.

Read M7_UNIVERSAL_SELECTOR_TASK_20260915.md for the full original selector
scope, M7_GENERATION_REVIEWED_MODULE_20260915.md and
M7_SELECTION_REVIEWED_MODULE_20260915.md for the first two module arguments.
They received dual reviews as scoped modules in run-efc8r824, but their
composition and the compact replacement here require fresh full review.
Check invoked arguments directly; the review status is not a premise.

## Proposed compact exact orbit-prefix count
G=C_N^2 semidirect(U(N) x C_2) acts on ordered pairs. Let x=(A,B)
be one stored anchored representative. Write h_x=|Stab_G(x)|.

For a binary prefix p, let P_A and P_B be its blockwise selected/allowed
conditions (including anchor zero). For unit u and swap epsilon, set
X=u A_epsilon, Y=u B_epsilon and
    a(u,epsilon,p)=#{s in C_N: X+s satisfies P_A},
    b(u,epsilon,p)=#{t in C_N: Y+t satisfies P_B}.
Each number is computed by a SINGLE-block translation loop.
Let F_u=gcd(poly(X),poly(Y),x^N+1). Independent translations and swap
do not change F_u; common units may change it.

For exact sector F, proposed identity:
    O_x(F,p) = (1/h_x) sum_{u,epsilon} 1[F_u=F]
                                   a(u,epsilon,p)*b(u,epsilon,p).
For a sector set, use its membership indicator; for all sectors use 1.
Prove this counts DISTINCT anchored orbit members satisfying the prefix:
each orbit element has exactly h_x group preimages.
Compute h_x by the SAME factorized numerator with the target block
conditions equal to A and B exactly, and without sector filtering.
Do not enumerate translation pairs to compute either numerator or h_x.
Handle N=1, w=1, stabilizers, periodic supports and full multiplicities.

Canonicalization likewise needs no pair-product scan: for each unit take
each block's least translate independently, order the pair, and minimize
over units. Supply reconstructible group actions when needed.

For already emitted DISTINCT canonical classes x_1,...,x_q, replace the
expanded-set residual by
    R_F(p)=C_F(p)-sum_j O_{x_j}(F,p),
where C_F is M5's exact conditional completion count.
Prove nonnegativity, branch partition, positive-leaf recovery, one new
class per recovery, termination and zero-residual coverage. Keep all
transported signatures; exact-F queries use orbit-intersection semantics.

This still performs character sums, loops over units and single-block
translations, and visits every relevant quotient class. Account for all
costs and potentially huge output. The stronger intended guarantee is:
no Cartesian enumeration of raw support pairs, no traversal of all positive
leaves, and no explicit materialization of full pair orbits. A proof must
establish those algorithmic properties, not just assert efficiency.

## Complete original-M7 composition
Compose this compact generator with M6 exact distance and the selection
module, explicitly proving no missing optimum, ties, empty queries,
k=0 conventions, literal-F realizing witnesses and actual optimal placements.
Generation must cover all structural candidates before distance/locality
filtering; excluded classes need replayable label/nonwinner evidence.
A verifier must recompute M5 arithmetic, compact orbit counts and M6 labels
or their exact trace recurrence as necessary. Hashes alone are insufficient.
For arbitrary extra predicates/objectives state total computability and
certificate interfaces; implement the default k/d/locality query language
without unsolved oracles. Do not restrict arbitrary N or w to old catalogues.

Return an exact original-M7 acceptance assessment or a precise unmet clause.
All-span polynomial time, M8, practical superiority and Lean are not gates.

## Implementation and finite evidence
scripts/m7_selector_compact_20260915.py implements a finite prototype with
the compact numerator, stabilizer division and residual. Its imported files
are scripts/m7_oracle_m5_20260915.py and scripts/m7_distance_m6_20260915.py.
The primary generator has no expanded-orbit fallback. Raw enumeration
functions are independent finite validation only, not production generation.
The prototype's query language is a tested subset of the full theorem and
need not implement every extension; disclose that boundary.
evidence/m7_selector_compact_validation_20260915.json reports 29 generation
cases and 75 optimization queries, including signature transport at N=7,
ties and empty results. These are NOT symbolic proof premises.
Inspect or independently validate code when allowed. Main writes a report;
pure validate() returns results without writing. Do not invent execution.

Freeze one self-contained final composition and obtain fresh independent
dual reviews of that unchanged artifact and original-M7 scope.
