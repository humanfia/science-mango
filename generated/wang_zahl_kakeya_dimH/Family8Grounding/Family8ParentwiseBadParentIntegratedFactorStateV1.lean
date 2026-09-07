import Family8Grounding.Family8ParentwiseBadParentFactorListStateV1
import Family8Grounding.Family8ParentwiseBadParentFreshProxyFrostmanV2
import Family8Grounding.Family8ParentwiseBadParentMassAwareActualFactorListV1
import Mathlib.Tactic

/-!
# Integrated positive state for one parentwise bad factor

This module joins the three concrete outputs already available at one literal
bad parent:

* the actual coarse/fresh-child factor-list successor and its exact count and
  radius products;
* unit-ball Frostman control of that same selected fresh child; and
* source-shading correlation for the actual parent-aggregated coarse atom.

The selected fibre remains a field of the existing successor state, so every
additional conclusion below is definitionally about the same `S`, `q`, and
`selected`.  No selector, hierarchy, or analytic callback is added here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentIntegratedFactorStateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorListStateV1
open Family8ParentwiseBadParentFreshProxyFrostmanV2
open Family8ParentwiseBadParentMassAwareActualFactorListV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- One concrete successor state enriched by the object-level facts required
by the next recursive/analytic layer. -/
structure IntegratedBadParentFactorState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower C : ENNReal) where
  factorState : ParentwiseBadParentFactorListState
    D S left right hrho hrhoOne q lower C
  fresh_unitBall_frostman :
    IsFrostmanIn
      (badParentFreshProxyFrostmanConstant
        S D.shading hrho hrhoOne q factorState.selected
          (lower *
            (16 * selectedParentLowCFFreshLoss
              S hrho hrhoOne q lower)))
      (badParentFreshSuccessorDatum
        S D.shading hrho hrhoOne q factorState.selected).family.bodyFamily
      unitBallBody
  coarse_shadingMass_le_source :
    (activeCoarseAggregatedDatum D S).shading.shadingMass <=
      (activeFineShading S D.shading).shadingMass
  coarse_shadedUnion_eq_source :
    (activeCoarseAggregatedDatum D S).shading.shadedUnion =
      (activeFineShading S D.shading).shadedUnion
  coarse_averageMultiplicity_le_source :
    (activeCoarseAggregatedDatum D S).shading.averageMultiplicity <=
      (activeFineShading S D.shading).averageMultiplicity

/-- Callback-free producer of the integrated state.  The unit-ball theorem is
applied to the exact `selected` field produced by the factor-list state. -/
theorem exists_integratedBadParentFactorState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hD : D.IsAdmissible)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower C : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower)
    (huniform : IsCUniform S C) :
    Nonempty (IntegratedBadParentFactorState
      D S left right hrho hrhoOne q lower C) := by
  obtain ⟨X⟩ := exists_parentwiseBadParentFactorListState
    D S left right hD hrho hrhoOne hdeltaRho q hlowerTop hbad huniform
  refine ⟨{
    factorState := X
    fresh_unitBall_frostman := ?_
    coarse_shadingMass_le_source :=
      badParentAggregatedCoarse_shadingMass_le_activeFine D S
    coarse_shadedUnion_eq_source :=
      badParentAggregatedCoarse_shadedUnion_eq_activeFine D S
    coarse_averageMultiplicity_le_source :=
      badParentAggregatedCoarse_averageMultiplicity_le_activeFine D S }⟩
  exact badParentFreshSuccessorDatum_isFrostmanIn_unitBall_of_source
    S D.shading hD.delta_pos hD.delta_le_half hrho hrhoOne hdeltaRho
      q X.selected X.selected_nonempty X.child_frostman X.child_admissible

#print axioms IntegratedBadParentFactorState
#print axioms exists_integratedBadParentFactorState

end
end Family8ParentwiseBadParentIntegratedFactorStateV1
