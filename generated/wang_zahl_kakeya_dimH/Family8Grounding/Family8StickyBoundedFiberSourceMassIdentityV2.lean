import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyBoundedFiberSourceMassIdentityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8StickyBoundedFiberPartitionCoreV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8NormalizedCrossingSourceTauShadingV2

noncomputable section

/-!
# Source mass of the bounded-fibre coarse partition

The bounded partition changes only the quantitative branching fields of the
literal Sticky factorization. Its fine index set is still the cover's active
fine set, so its source shading has exactly the actual active-fine mass.

V1 is a failed namespace draft and is not imported.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem boundedFiberCoarseTubePartition_sourceActiveFineShading_mass_eq
    (S : StickyScaleCover fine rho)
    (hscale : delta ≤ rho) (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ M)
    (Y : Shading fine.bodyFamily) :
    (sourceActiveFineShading
      (boundedFiberCoarseTubePartition S hscale hcoarse M hM).asConvexFactorization
      Y).shadingMass = (activeFineShading S Y).shadingMass := by
  rw [sourceActiveFineShading_shadingMass]
  change
    (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass =
      (activeFineShading S Y).shadingMass
  exact (activeFineShading_shadingMass_eq_restrictTo S Y).symm

#print axioms
  boundedFiberCoarseTubePartition_sourceActiveFineShading_mass_eq

end
end Family8StickyBoundedFiberSourceMassIdentityV2
