import Family8Grounding.Family8EndpointLongCoreHalfRadiusThresholdV2
import Family8Grounding.Family8NormalizedLongCoreShadingAwareCanonicalBufferedInputV1
import Family8Grounding.Family8NormalizedLongCoreShadingAwareFullRefinementMassV2
import Family8Grounding.Family8PositiveCarrierShadingRestrictionV4
import Mathlib.Tactic

/-!
# Callback-free endpoint buffered-input data on the full refinement, V3

This packages every dependent side condition required by the literal
shading-aware Eq. (45/46) input.  Keeping the proof-dependent fields in a
small structure gives downstream scalar producers stable projections while
preserving the exact selected objects.

V1 and V2 attempted to infer the very large proof-dependent final input type
directly and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreHalfRadiusThresholdV2
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareCanonicalBufferedInputV1
open Family8NormalizedLongCoreShadingAwareFullRefinementMassV2
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8PositiveCarrierShadingRestrictionV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma etaF : Real}

/-- All proof-dependent side conditions of the endpoint canonical buffered
input, tied to the literal full-refinement long witness. -/
structure EndpointFullRefinementShadingAwareBufferedInputData
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (hdeltaOne : delta ≤ 1)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta
        (endpointScaleSequence delta hdeltaOne)) where
  epsilonHalf : P.epsilon ≤ 1 / 2
  fineNonempty :
    (fullRefinementDatum D).family.refinement.refined.Nonempty
  activeMassNeZero : coreShadingAwareActiveShadingMass
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
    C (endpointScaleSequence delta hdeltaOne) P W epsilonHalf ≠ 0
  radiusHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹

/-- Frostman density and the explicit endpoint threshold construct all four
side conditions without callbacks. -/
theorem endpointFullRefinementShadingAwareBufferedInputData
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (hdeltaOne : delta ≤ 1)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta
        (endpointScaleSequence delta hdeltaOne))
    (hF : FrostmanHypotheses D etaF)
    (hsmall : delta ≤ endpointLongCoreHalfRadiusThreshold P) :
    EndpointFullRefinementShadingAwareBufferedInputData
      D hD P C hdeltaOne W := by
  have hepsilonHalf : P.epsilon ≤ 1 / 2 := by
    have hgapOne : gamma - beta < 1 := by linarith
    have hgap := P.epsilon_gap
    nlinarith [P.epsilon_pos]
  have hmass : coreShadingAwareActiveShadingMass
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C (endpointScaleSequence delta hdeltaOne) P W
        hepsilonHalf ≠ 0 :=
    coreShadingAwareActiveShadingMass_ne_zero_of_fullRefinement
      D hD C (endpointScaleSequence delta hdeltaOne) P W
        hepsilonHalf hF
  have hsourceMass : D.shading.shadingMass ≠ 0 := by
    rw [← coreShadingAwareActiveShadingMass_fullRefinement
      D hD C (endpointScaleSequence delta hdeltaOne) P W
        hepsilonHalf]
    exact hmass
  have hfine :
      (fullRefinementDatum D).family.refinement.refined.Nonempty := by
    rw [fullRefinementDatum_refined]
    obtain ⟨i, _hi⟩ :=
      positiveCarrierIndices_nonempty_of_shadingMass_ne_zero
        D.shading hsourceMass
    exact ⟨i, Finset.mem_univ i⟩
  exact
    { epsilonHalf := hepsilonHalf
      fineNonempty := hfine
      activeMassNeZero := hmass
      radiusHalf := canonicalBufferedRadius_le_half_of_endpointSmall
        P hbeta hgamma hdeltaOne W hsmall }

#print axioms endpointFullRefinementShadingAwareBufferedInputData

end

end Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV3
