import Family8Grounding.Family8ParentwiseBadParentActualFactorListSuccessorV1
import Family8Grounding.Family8StickyActiveCoarseAdmissibleChildV1
import Family8Grounding.Family8ParentAggregatedAverageMultiplicityMonotonicityV2
import Mathlib.Tactic

/-!
# Mass-aware actual factor-list replacement at one bad parent

The actual-list successor uses `activeCoarseAggregatedDatum`, so the coarse
factor remembers the supplied source shading grouped by its literal Sticky
parents.  This file is the theorem layer over that core list: it records the
mass, shaded-union, and average-multiplicity correlation and combines it with
the callback-free same-parent replacement producer.

The same literal bad parent `q` supplies the fresh affine child.  The exact
`3/64` radius coefficient and both directions of the honest cardinality
product comparison are transported through an arbitrary surrounding factor
list.  No successor callback and no synthetic coherent cover occurs here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentMassAwareActualFactorListV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParentAggregatedAverageMultiplicityMonotonicityV2
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open Family8StickyUniformCountLossV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  (D : ActualTubeDatum delta iota)

/-! ## Explicit absorption of the fixed scale coefficient -/

/-- The exact `3/64` radius coefficient is inverted with the displayed
`64/3` loss; it is not silently treated as one. -/
theorem badParentSourceFactorList_radiusProduct_eq_fixedLoss_mul
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) :
    factorRadiusProduct (badParentSourceFactorList D left right S) =
      (64 / 3 : NNReal) *
        factorRadiusProduct
          (badParentSuccessorFactorList
            D left right S hrho hrhoOne q selected) := by
  rw [badParentSuccessorFactorList_radiusProduct]
  ring_nf

/-! ## Source-shading correlation on the actual coarse atom -/

theorem badParentAggregatedCoarse_shadingMass_le_activeFine
    (S : StickyScaleCover D.family rho) :
    (activeCoarseAggregatedDatum D S).shading.shadingMass <=
      (activeFineShading S D.shading).shadingMass := by
  exact parentAggregatedShading_shadingMass_le S D.shading

theorem badParentAggregatedCoarse_shadedUnion_eq_activeFine
    (S : StickyScaleCover D.family rho) :
    (activeCoarseAggregatedDatum D S).shading.shadedUnion =
      (activeFineShading S D.shading).shadedUnion := by
  exact parentAggregatedShading_shadedUnion S D.shading

theorem badParentAggregatedCoarse_averageMultiplicity_le_activeFine
    (S : StickyScaleCover D.family rho) :
    (activeCoarseAggregatedDatum D S).shading.averageMultiplicity <=
      (activeFineShading S D.shading).averageMultiplicity := by
  exact
    Family8ParentAggregatedAverageMultiplicityMonotonicityV2.StickyScaleCover.parentAggregatedShading_averageMultiplicity_le_activeFineShading
      S D.shading

/-! ## Callback-free mass-aware one-step producer -/

theorem exists_badParent_massAwareActualFactorListSuccessor
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower C : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower)
    (huniform : IsCUniform S C) :
    exists selected : Finset {i // i ∈ S.fiber q.1},
      selected.Nonempty /\
      (badParentFreshSuccessorDatum
        S D.shading hrho hrhoOne q selected).IsAdmissible /\
      IsFrostmanIn
        (lower *
          (16 * selectedParentLowCFFreshLoss S hrho hrhoOne q lower))
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q) /\
      (badParentRescaledFibreDatum
        S D.shading hrho hrhoOne q).shading.shadingMass <=
        badParentFreshRetentionLoss S hrho hrhoOne q selected lower *
          (badParentFreshSuccessorDatum
            S D.shading hrho hrhoOne q selected).shading.shadingMass /\
      factorRadiusProduct
          (badParentSuccessorFactorList
            D left right S hrho hrhoOne q selected) =
        (3 / 64 : NNReal) *
          factorRadiusProduct (badParentSourceFactorList D left right S) /\
      factorCardProduct
          (badParentSuccessorFactorList
            D left right S hrho hrhoOne q selected) <=
        C * factorCardProduct
          (badParentSourceFactorList D left right S) /\
      factorCardProduct (badParentSourceFactorList D left right S) <=
        (C * badParentFreshRetentionLoss
            S hrho hrhoOne q selected lower) *
          factorCardProduct
            (badParentSuccessorFactorList
              D left right S hrho hrhoOne q selected) /\
      (activeCoarseAggregatedDatum D S).shading.shadingMass <=
        (activeFineShading S D.shading).shadingMass /\
      (activeCoarseAggregatedDatum D S).shading.shadedUnion =
        (activeFineShading S D.shading).shadedUnion /\
      (activeCoarseAggregatedDatum D S).shading.averageMultiplicity <=
        (activeFineShading S D.shading).averageMultiplicity := by
  obtain ⟨selected, hselected, hadmissible, _hfreshTop,
      hFrostman, hmass, P⟩ :=
    exists_badParent_freshFactorReplacement_with_product
      S D.shading hdelta hdeltaHalf hrho hrhoOne hdeltaRho q
        hlowerTop hbad huniform
  refine ⟨selected, hselected, hadmissible, hFrostman, hmass,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact badParentSuccessorFactorList_radiusProduct
      D left right S hrho hrhoOne q selected
  · exact badParentSuccessorFactorList_cardProduct_le
      D left right S hrho hrhoOne q selected lower C P
  · exact badParentSourceFactorList_cardProduct_le
      D left right S hrho hrhoOne q selected lower C P
  · exact badParentAggregatedCoarse_shadingMass_le_activeFine D S
  · exact badParentAggregatedCoarse_shadedUnion_eq_activeFine D S
  · exact badParentAggregatedCoarse_averageMultiplicity_le_activeFine D S

#print axioms badParentSuccessorFactorList_radiusProduct
#print axioms badParentSourceFactorList_radiusProduct_eq_fixedLoss_mul
#print axioms badParentSuccessorFactorList_cardProduct_le
#print axioms badParentSourceFactorList_cardProduct_le
#print axioms badParentAggregatedCoarse_shadingMass_le_activeFine
#print axioms badParentAggregatedCoarse_shadedUnion_eq_activeFine
#print axioms badParentAggregatedCoarse_averageMultiplicity_le_activeFine
#print axioms exists_badParent_massAwareActualFactorListSuccessor

end
end Family8ParentwiseBadParentMassAwareActualFactorListV1
