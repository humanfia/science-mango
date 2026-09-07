import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickySourceMassFactorizationRoundTripV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover

noncomputable section

/-!
# Exact factorization round trip for the source-mass partition

The source-mass constructor only supplies the nonempty-coarse proof required
by `toCoarseTubePartition`.  Its fine set, coarse set, parent map, and fibres
are the literal fields of the original Sticky cover.  Thus its associated
factorization is the same object as `toConvexFactorization`, up to proof
irrelevance.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

theorem sourceMass_asConvexFactorization_eq_toConvexFactorization
    (S : StickyScaleCover fine rho) (hscale : delta <= rho)
    (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0) :
    (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization =
      toConvexFactorization S := by
  rfl

#print axioms sourceMass_asConvexFactorization_eq_toConvexFactorization

end
end Family8StickySourceMassFactorizationRoundTripV1
