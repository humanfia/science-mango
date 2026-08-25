import FamilyStickyGrounding.FamilyStickyRandomWZLineParameterGeometryV1
import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyHierarchyLevelWZSeparationCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring

/-!
# Minimal hierarchy-level WZ separation source interface

The collision random-motion argument uses only endpoint-parameter separation
on each refined hierarchy level.  Keeping that exact datum in a dedicated
module prevents the hierarchy collision adapters from importing the legacy
test-card packing route or any of its computational proof machinery.
-/

/-- The exact hierarchy-level datum consumed by the collision certificates:
WZ endpoint-parameter separation on every refined level. -/
structure HierarchyLevelWZSeparationData
    {depth : Nat} {nominalRadius : Nat -> NNReal}
    {Index : Nat -> Type*}
    [forall l, DecidableEq (Index l)]
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) : Prop where
  separated : forall (l : Nat) (_hl : l <= depth),
    Set.Pairwise ((H.family l).refinement.refined : Set (Index l))
      fun i j =>
        FamilyStickyRandomWZLineParameterGeometryV1.WZEndpointParameterSeparated
          ((H.effectiveFamily l).tubes i)
          ((H.effectiveFamily l).tubes j)

end FamilyStickyHierarchyLevelWZSeparationCoreV1
