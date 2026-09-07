import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaConnectorV3
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1

/-!
# Selected-parent plank buckets as literal ExactAssembly induced data, V2

The parent shading used by the selected-parent plank construction is not a
new analytic object: on every active parent it is exactly the induced shading
of the convex factorization carried by the same `StickyScaleCover`.  This file
records that identity at the carrier level and then follows it through the
actual block restriction, affine normalization, and side-shape bucket.

This is deliberately only a data-identity bridge.  It does not identify a
whole plank bucket with an `ExactAssembly.sourceFineLevelShading`: the latter
has an additional pointwise fine-multiplicity-level restriction.  Such an
identification needs a genuine saturation theorem for the chosen assembly.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyInducedIdentityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickyScaleCoverFrostmanInheritanceV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Restrict the induced shading of the cover's literal convex factorization
to the genuinely active coarse subtype. -/
def activeInducedShading (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) : Shading S.activeCoarseFamily :=
  selectedCoarseShading ((toConvexFactorization S).inducedShading Y)
    S.activeCoarse

/-- On each active parent, the literal induced carrier is exactly the parent
aggregation used by the selected-parent plank construction. -/
theorem activeInducedShading_carrier_eq_parentAggregatedShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (p : ActiveParentIndex S) :
    (activeInducedShading S Y).carrier p =
      (parentAggregatedShading S Y).carrier p := by
  ext x
  constructor
  · intro hx
    have hx' :
        x ∈ ((toConvexFactorization S).inducedShading Y).carrier p.1 := hx
    obtain ⟨_hp, i, hiFiber, hxi⟩ :=
      ((toConvexFactorization S).mem_inducedShading_carrier_iff
        Y p.1 x).1 hx'
    have hiFine : i ∈ S.activeFine := by
      exact (toConvexFactorization S).index.fiber_subset_fine p.1 hiFiber
    let ii : {i // i ∈ S.activeFine} := ⟨i, hiFine⟩
    have hiiFiber : ii ∈ (activeIndexFactorization S).fiber p := by
      rw [IndexFactorization.mem_fiber]
      refine ⟨Finset.mem_univ ii, ?_⟩
      apply Subtype.ext
      exact (IndexFactorization.mem_fiber
        (toConvexFactorization S).index i p.1).1 hiFiber |>.2
    exact Set.mem_iUnion.mpr
      ⟨ii, Set.mem_iUnion.mpr ⟨hiiFiber, hxi⟩⟩
  · intro hx
    obtain ⟨ii, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hiiFiber, hxiY⟩ := Set.mem_iUnion.mp hxi
    have hparent :=
      (IndexFactorization.mem_fiber (activeIndexFactorization S) ii p).1
        hiiFiber
    have hiFiber : ii.1 ∈ (toConvexFactorization S).index.fiber p.1 := by
      rw [IndexFactorization.mem_fiber]
      exact ⟨ii.2, congrArg Subtype.val hparent.2⟩
    exact ((toConvexFactorization S).mem_inducedShading_carrier_iff
      Y p.1 x).2 ⟨p.2, ii.1, hiFiber, hxiY⟩

/-- The actual selected-parent block shading is literally the restriction of
the cover-induced shading, at every carrier. -/
theorem selectedParentActualShading_carrier_eq_inducedShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (p : {p // p ∈ B}) :
    (selectedParentActualShading S Y B).carrier p =
      ((toConvexFactorization S).inducedShading Y).carrier p.1.1 := by
  calc
    (selectedParentActualShading S Y B).carrier p =
        (parentAggregatedShading S Y).carrier p.1 := rfl
    _ = (activeInducedShading S Y).carrier p.1 :=
      (activeInducedShading_carrier_eq_parentAggregatedShading
        S Y p.1).symm
    _ = ((toConvexFactorization S).inducedShading Y).carrier p.1.1 := rfl

/-- After the actual affine normalization and side-shape restriction, every
bucket carrier is still the literal affine image of the corresponding
induced carrier. -/
theorem selectedParentPlankBucketShading_carrier_eq_inducedShading_image
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (q : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    (selectedParentPlankBucketShading e S Y B hrho label).carrier q =
      bucketNormalizedAffineEquiv e label ''
        ((toConvexFactorization S).inducedShading Y).carrier q.1.1.1 := by
  change bucketNormalizedAffineEquiv e label ''
      (parentAggregatedShading S Y).carrier q.1.1 = _
  rw [← activeInducedShading_carrier_eq_parentAggregatedShading
    S Y q.1.1]
  rfl

/-- ExactAssembly specialization of the preceding carrier identity.  The
source supplied to the plank bucket is the actual final refinement; no new
shading or multiplicity conclusion is assumed. -/
theorem exactAssembly_selectedParentPlankBucket_carrier_eq_inducedShading_image
    {loss : Nat} (S : StickyScaleCover fine rho)
    {Y : Shading fine.bodyFamily}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (toConvexFactorization S) Y loss)
    (e : Space ≃ᵃ[Real] Space)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (q : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    (selectedParentPlankBucketShading e S A.refinement.shading
      B hrho label).carrier q =
      bucketNormalizedAffineEquiv e label ''
        ((toConvexFactorization S).inducedShading
          A.refinement.shading).carrier q.1.1.1 :=
  selectedParentPlankBucketShading_carrier_eq_inducedShading_image
    e S A.refinement.shading B hrho label q

#print axioms activeInducedShading_carrier_eq_parentAggregatedShading
#print axioms selectedParentActualShading_carrier_eq_inducedShading
#print axioms
  selectedParentPlankBucketShading_carrier_eq_inducedShading_image
#print axioms
  exactAssembly_selectedParentPlankBucket_carrier_eq_inducedShading_image

end

end Family8SelectedParentExactAssemblyInducedIdentityV2
