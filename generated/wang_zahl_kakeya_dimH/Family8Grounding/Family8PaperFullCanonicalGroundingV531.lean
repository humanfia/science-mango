import Family8Grounding.Family8PaperFullCanonicalGroundingV530
import Family8Grounding.Family8GreedySuppliedCoverJointParallelBoundV1
import Family8Grounding.Family8EpsilonExtremalGreedyJointPlankPackageV1

/-!
# Full canonical grounding checkpoint V531

The genuine supplied cover and the full-convex greedy partition now have a
single epsilon-extremal package.  The occupied joint cover keeps literal
supplied-parent provenance, has both active-card and product cardinality
bounds, and has parallel clusters bounded by
`P.length * parallelLoss`.  Its active coarse scale mass is bounded by
`1024 * coarseDeltaMax`.

The same witness also returns a nonempty normalized greedy-winner plank
bucket.  Every selected winner uses one common normalization scalar in
`[1/1024, 1]`, and the returned structure retains its memberwise plank
certificate.

This is an honest compatibility checkpoint, not a proof of the remaining
Katz--Tao geometry.  Splitting a greedy block by supplied parents does not
make each joint fibre inherit the whole block's maximal-density/Frostman
property.  Moreover, a parent parallel-cluster bound alone does not yet give
the arbitrary-convex-body concentration estimate required by `IsKatzTao`,
and the current epsilon-extremal interface supplies no upper bound on
`parallelLoss`.  Therefore no unconditional LongCore, DSO, `mainLemmaOne`,
or full paper theorem is claimed here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV531

open Family8GreedySuppliedCoverJointParallelBoundV1
open Family8EpsilonExtremalGreedyJointPlankPackageV1

#print axioms jointParallelCluster
#print axioms jointParallelCluster_card_le_blocks_mul_supplied
#print axioms jointParallelCluster_card_le_length_mul
#print axioms exists_epsilonExtremalGreedyJointPlankPackage

end Family8PaperFullCanonicalGroundingV531
